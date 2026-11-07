//! Test-only reference decoder and encoder.
//!
//! This is a frozen copy of the decoder as it was before any performance work. It does NOT use
//! [crate::gf]. It has its own slow, table-free GF(2^8) arithmetic (built at run time), so
//! changes to the optimized code cannot change it. Do not optimize this file.
//!
//! It shares only [crate::dual_basis] (the CCSDS lookup tables) and the constants and result
//! types of the crate root.
use crate::{Block, RSState, FCR, GEN, N, PARITY_LEN, PRIM};
use std::sync::OnceLock;

/// Reference GF(2^8) arithmetic. Same behavior as `crate::gf`, including the edge cases
/// (`pow` of zero, `inv` of zero) that the decoder never reaches in normal use.
mod rgf {
    use super::*;

    /// Carry-less multiply, reduced by the primitive polynomial.
    fn mult_slow(mut x: u32, mut y: u32) -> u32 {
        let mut r = 0;
        while y > 0 {
            if y & 1 > 0 {
                r ^= x;
            }
            y >>= 1;
            x <<= 1;
            if x & 256 != 0 {
                x ^= PRIM as u32;
            }
        }
        r
    }

    /// (exp, log). exp has 510 entries so no modulo is needed for a sum of two logs.
    fn tables() -> &'static ([u8; 510], [u8; 256]) {
        static T: OnceLock<([u8; 510], [u8; 256])> = OnceLock::new();
        T.get_or_init(|| {
            let mut exp = [0u8; 510];
            let mut log = [0u8; 256];
            let mut x = 1u32;
            for i in 0..255 {
                exp[i] = x as u8;
                exp[i + 255] = x as u8;
                log[x as usize] = i as u8;
                x = mult_slow(x, GEN as u32);
            }
            assert_eq!(x, 1, "GEN must have order 255");
            (exp, log)
        })
    }

    pub fn mult(x: u8, y: u8) -> u8 {
        if x == 0 || y == 0 {
            return 0;
        }
        let (exp, log) = tables();
        exp[log[x as usize] as usize + log[y as usize] as usize]
    }

    pub fn div(x: u8, y: u8) -> u8 {
        if y == 0 {
            panic!("zero division");
        }
        if x == 0 {
            return 0;
        }
        let (exp, log) = tables();
        exp[(log[x as usize] as usize + 255 - log[y as usize] as usize) % 255]
    }

    pub fn pow(x: u8, power: i32) -> u8 {
        let mut power = power;
        if power < 0 {
            power = (255 - (-power % 255)) % 255;
        }
        let (exp, log) = tables();
        exp[(log[x as usize] as i32 * power % 255) as usize]
    }

    pub fn inv(x: u8) -> u8 {
        let (exp, log) = tables();
        exp[255 - log[x as usize] as usize]
    }

    pub fn poly_scale(p: &[u8], x: u8) -> Vec<u8> {
        p.iter().map(|c| mult(*c, x)).collect()
    }

    pub fn poly_add(p: &[u8], q: &[u8]) -> Vec<u8> {
        let l = p.len().max(q.len());
        let mut r = vec![0u8; l];
        for i in 0..p.len() {
            r[i + l - p.len()] = p[i];
        }
        for i in 0..q.len() {
            r[i + l - q.len()] ^= q[i];
        }
        r
    }

    pub fn poly_mult(p: &[u8], q: &[u8]) -> Vec<u8> {
        let mut r = vec![0u8; p.len() + q.len() - 1];
        for j in 0..q.len() {
            for i in 0..p.len() {
                r[i + j] ^= mult(p[i], q[j]);
            }
        }
        r
    }

    pub fn poly_eval(p: &[u8], x: u8) -> u8 {
        let mut y = p[0];
        for c in &p[1..] {
            y = mult(y, x) ^ *c;
        }
        y
    }

    pub fn poly_div(dividend: &[u8], divisor: &[u8]) -> (Vec<u8>, Vec<u8>) {
        let mut out = dividend.to_vec();
        for i in 0..(dividend.len() - divisor.len() - 1) {
            let coef = out[i];
            if coef != 0 {
                for j in 1..divisor.len() {
                    if divisor[j] != 0 {
                        out[i + j] ^= mult(divisor[j], coef);
                    }
                }
            }
        }
        let mid = dividend.len() - divisor.len() + 1;
        let (head, tail) = out.split_at(mid);
        (head.to_vec(), tail.to_vec())
    }
}

use rgf as gf;

fn correct_errata(input: &[u8], synd: &[u8], errpos: &[i32]) -> Result<Vec<u8>, &'static str> {
    let coef_pos: Vec<i32> = errpos.iter().map(|p| input.len() as i32 - 1 - p).collect();

    let errloc = find_errata_locator(&coef_pos);
    let mut rev_synd = synd.to_owned();
    rev_synd.reverse();
    let mut erreval = find_error_evaluator(&rev_synd, &errloc, errloc.len() as i32 - 1);
    erreval.reverse();

    let x: Vec<u8> = coef_pos
        .iter()
        .map(|p| gf::pow(GEN, -(N as i32 - p)))
        .collect();

    let mut e = vec![0u8; input.len()];
    for (i, xi) in x.iter().enumerate() {
        let xi_inv = gf::inv(*xi);
        let mut errloc_prime = 1u8;
        for (j, xj) in x.iter().enumerate() {
            if j != i {
                errloc_prime = gf::mult(errloc_prime, 1 ^ gf::mult(xi_inv, *xj));
            }
        }

        let mut erreval_rev = erreval.clone();
        erreval_rev.reverse();
        let mut y = gf::poly_eval(&erreval_rev, xi_inv);
        y = gf::mult(gf::pow(*xi, 1 - FCR), y);

        if errloc_prime == 0 {
            return Err("failed to find error magnitude");
        }

        e[errpos[i] as usize] = gf::div(y, errloc_prime);
    }

    Ok(gf::poly_add(input, &e))
}

fn find_errata_locator(errpos: &[i32]) -> Vec<u8> {
    let mut errloc = vec![1u8];
    for p in errpos.iter() {
        let y = gf::poly_add(&[1u8], &[gf::pow(GEN, *p), 0]);
        errloc = gf::poly_mult(&errloc, &y);
    }
    errloc
}

fn find_error_evaluator(synd: &[u8], errloc: &[u8], n: i32) -> Vec<u8> {
    let mut divisor = vec![0u8; n as usize + 2];
    divisor[0] = 1;
    let (_, rem) = gf::poly_div(&gf::poly_mult(synd, errloc), &divisor);
    rem
}

fn find_errors(errloc: &[u8]) -> Vec<i32> {
    let mut errpos = Vec::with_capacity(errloc.len() - 1);
    for i in 0..N as i32 {
        if gf::poly_eval(errloc, gf::pow(GEN, i)) == 0 {
            errpos.push(N as i32 - 1 - i);
        }
    }
    errpos
}

fn find_error_locator(synd: &[u8], parity_len: usize) -> Vec<u8> {
    let mut errloc = vec![1u8];
    let mut oldloc = vec![1u8];
    let synd_shift = synd.len().saturating_sub(parity_len);
    for i in 0..parity_len {
        let k = i + synd_shift;
        let mut delta = synd[k];
        for j in 1..errloc.len() {
            delta ^= gf::mult(errloc[errloc.len() - j - 1], synd[k - j]);
        }
        oldloc.push(0);
        if delta != 0 {
            if oldloc.len() > errloc.len() {
                let newloc = gf::poly_scale(&oldloc, delta);
                oldloc = gf::poly_scale(&errloc, gf::inv(delta));
                errloc = newloc;
            }
            errloc = gf::poly_add(&errloc, &gf::poly_scale(&oldloc, delta));
        }
    }
    while !errloc.is_empty() && errloc[0] == 0 {
        errloc.remove(0);
    }
    errloc
}

fn forney_syndromes(synd: &[u8], pos: &[i32], nmess: i32) -> Vec<u8> {
    let mut fsynd = synd[1..].to_vec();
    for p in pos {
        let x = gf::pow(GEN, nmess - 1 - p);
        for j in 0..fsynd.len() - 1 {
            fsynd[j] = gf::mult(fsynd[j], x) ^ fsynd[j + 1];
        }
    }
    fsynd
}

pub fn calc_syndromes(input: &[u8], parity_len: usize) -> Vec<u8> {
    let mut synd = vec![0u8; parity_len + 1];
    for i in 0..parity_len {
        synd[i + 1] = gf::poly_eval(input, gf::pow(GEN, i as i32 + FCR));
    }
    synd
}

fn uncorrectable(msg: String) -> Block {
    Block {
        state: RSState::Uncorrectable(msg),
        message: None,
    }
}

/// Reference version of [crate::correct_message].
pub fn correct_message(input: &[u8]) -> Block {
    if input.len() != N as usize {
        return uncorrectable("invalid input".to_owned());
    }
    let out = crate::dual_basis::to_conv(input);

    let synd = calc_syndromes(&out, PARITY_LEN);
    if synd.iter().all(|s| *s == 0) {
        return Block {
            state: RSState::Ok,
            message: Some(input.to_vec()),
        };
    }

    let fsynd = forney_syndromes(&synd, &[], out.len() as i32);
    let errloc = find_error_locator(&fsynd, PARITY_LEN);

    let num_errs = errloc.len() - 1;
    if num_errs * 2 > PARITY_LEN {
        return uncorrectable(format!(
            "too many errors to correct; expected no more than {:?}, found {:?}",
            PARITY_LEN / 2,
            num_errs
        ));
    }

    let mut errloc_rev = errloc.clone();
    errloc_rev.reverse();
    let errpos = find_errors(&errloc_rev);
    if errpos.len() != num_errs {
        return uncorrectable(format!(
            "failed to generate error positions; expected {} postions, got {}",
            num_errs,
            errpos.len()
        ));
    }

    let out = match correct_errata(&out, &synd, &errpos) {
        Err(err) => return uncorrectable(err.to_owned()),
        Ok(block) => block,
    };

    let synd = calc_syndromes(&out, PARITY_LEN);
    if synd.iter().any(|s| *s != 0) {
        return uncorrectable("failed to correct all errors".to_owned());
    }

    Block {
        state: RSState::Corrected(errloc.len() as i32 - 1),
        message: Some(crate::dual_basis::to_dual(&out)),
    }
}

/// Reference version of [crate::has_errors].
pub fn has_errors(msg: &[u8]) -> bool {
    let msg = crate::dual_basis::to_conv(msg);
    calc_syndromes(&msg, PARITY_LEN).iter().any(|s| *s != 0)
}

/// Systematic encoder. `msg` is 223 bytes in conventional representation. Returns a
/// 255 byte code block in conventional representation. Test only: it exists to make valid
/// code blocks with random content.
pub fn encode(msg: &[u8]) -> Vec<u8> {
    let k = N as usize - PARITY_LEN;
    assert_eq!(msg.len(), k);
    // g(x) = product of (x + a^(FCR+i)), highest degree first
    let mut g = vec![1u8];
    for i in 0..PARITY_LEN {
        g = gf::poly_mult(&g, &[1, gf::pow(GEN, i as i32 + FCR)]);
    }
    let mut out = msg.to_vec();
    out.extend_from_slice(&[0u8; PARITY_LEN]);
    for i in 0..k {
        let coef = out[i];
        if coef != 0 {
            for j in 1..g.len() {
                out[i + j] ^= gf::mult(g[j], coef);
            }
        }
    }
    out[..k].copy_from_slice(msg);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dual_basis::{to_conv, to_dual};

    /// Small deterministic generator (xorshift64*). Avoids a dependency.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn byte(&mut self) -> u8 {
            (self.next() >> 56) as u8
        }
        fn nonzero_byte(&mut self) -> u8 {
            loop {
                let b = self.byte();
                if b != 0 {
                    return b;
                }
            }
        }
    }

    /// A random valid code block in dual basis.
    fn random_block(rng: &mut Rng) -> Vec<u8> {
        let msg: Vec<u8> = (0..223).map(|_| rng.byte()).collect();
        to_dual(&encode(&msg))
    }

    /// Change `count` distinct positions to a different value.
    fn corrupt(rng: &mut Rng, block: &[u8], count: usize) -> Vec<u8> {
        let mut out = block.to_vec();
        let mut pos: Vec<usize> = (0..out.len()).collect();
        for i in 0..count {
            let j = i + (rng.next() % (pos.len() - i) as u64) as usize;
            pos.swap(i, j);
            out[pos[i]] ^= rng.nonzero_byte();
        }
        out
    }

    #[test]
    fn encoder_makes_valid_blocks() {
        let mut rng = Rng(1);
        for _ in 0..50 {
            let block = random_block(&mut rng);
            assert_eq!(block.len(), 255);
            assert!(!has_errors(&block));
            assert!(calc_syndromes(&to_conv(&block), PARITY_LEN)
                .iter()
                .all(|s| *s == 0));
        }
    }

    /// Checks the reference itself: up to 16 errors must be corrected exactly.
    #[test]
    fn reference_corrects_up_to_16_errors() {
        let mut rng = Rng(2);
        for count in 0..=16 {
            for _ in 0..25 {
                let good = random_block(&mut rng);
                let bad = corrupt(&mut rng, &good, count);
                let block = correct_message(&bad);
                if count == 0 {
                    assert_eq!(block.state, RSState::Ok);
                } else {
                    assert_eq!(block.state, RSState::Corrected(count as i32));
                }
                assert_eq!(block.message.as_deref(), Some(&good[..]), "count={count}");
            }
        }
    }

    /// Checks the reference itself: 17 or more errors must never report a wrong "correction"
    /// as the original block. (A rare miscorrection to another valid block is allowed by
    /// the code, so this only checks that the message is not silently wrong with state Ok.)
    #[test]
    fn reference_never_reports_ok_for_corrupt_block() {
        let mut rng = Rng(3);
        for count in 17..=24 {
            for _ in 0..25 {
                let good = random_block(&mut rng);
                let bad = corrupt(&mut rng, &good, count);
                assert_ne!(correct_message(&bad).state, RSState::Ok);
            }
        }
    }

    /// The optimized decoder must give the same state and message as the reference, for
    /// error counts below, at, and above the correction limit.
    #[test]
    fn decoder_matches_reference() {
        let mut rng = Rng(4);
        for count in 0..=24 {
            for _ in 0..40 {
                let good = random_block(&mut rng);
                let bad = corrupt(&mut rng, &good, count);

                let got = crate::correct_message(&bad);
                let want = correct_message(&bad);
                assert_eq!(got.state, want.state, "state, count={count}");
                assert_eq!(got.message, want.message, "message, count={count}");
                assert_eq!(
                    crate::has_errors(&bad),
                    has_errors(&bad),
                    "has_errors, count={count}"
                );
            }
        }
    }

    /// `correct_in_place` must match the reference state. The buffer must hold the corrected
    /// block when Corrected, and be unchanged otherwise.
    #[test]
    fn in_place_matches_reference() {
        let mut rng = Rng(6);
        for count in 0..=24 {
            for _ in 0..40 {
                let good = random_block(&mut rng);
                let bad = corrupt(&mut rng, &good, count);
                let want = correct_message(&bad);

                let mut buf = [0u8; 255];
                buf.copy_from_slice(&bad);
                let state = crate::correct_in_place(&mut buf);
                assert_eq!(state, want.state, "state, count={count}");
                match want.message {
                    Some(m) => assert_eq!(&buf[..], &m[..], "count={count}"),
                    None => assert_eq!(&buf[..], &bad[..], "unchanged, count={count}"),
                }
            }
        }
    }

    /// The error path patches single bytes and relies on the two dual basis tables being
    /// inverses of each other.
    #[test]
    fn dual_basis_tables_are_inverse() {
        for x in 0..=255u8 {
            assert_eq!(
                crate::dual_basis::dual_byte(crate::dual_basis::conv_byte(x)),
                x
            );
            assert_eq!(
                crate::dual_basis::conv_byte(crate::dual_basis::dual_byte(x)),
                x
            );
        }
    }

    /// The linear syndrome recheck must say yes for the true errors and no for anything else.
    /// The decoder tests do not reach this branch, so test the function directly.
    #[test]
    fn errata_recheck_is_exact() {
        let mut rng = Rng(8);
        for count in 1..=16 {
            for _ in 0..30 {
                let good = random_block(&mut rng);
                let bad = corrupt(&mut rng, &good, count);
                let pos: Vec<u8> = (0..255u8)
                    .filter(|p| good[*p as usize] != bad[*p as usize])
                    .collect();
                assert_eq!(pos.len(), count);
                let val: Vec<u8> = pos
                    .iter()
                    .map(|p| {
                        crate::dual_basis::conv_byte(bad[*p as usize])
                            ^ crate::dual_basis::conv_byte(good[*p as usize])
                    })
                    .collect();
                let s = crate::syndromes_dual(&bad);

                assert!(
                    crate::errata_clears_syndromes(&s, &pos, &val),
                    "true errors"
                );

                let mut wrong_val = val.clone();
                wrong_val[0] ^= 1;
                assert!(
                    !crate::errata_clears_syndromes(&s, &pos, &wrong_val),
                    "wrong value"
                );

                let mut wrong_pos = pos.clone();
                wrong_pos[0] = (wrong_pos[0] + 1) % 255;
                if !pos.contains(&wrong_pos[0]) {
                    assert!(
                        !crate::errata_clears_syndromes(&s, &wrong_pos, &val),
                        "wrong position"
                    );
                }

                if count > 1 {
                    assert!(
                        !crate::errata_clears_syndromes(&s, &pos[1..], &val[1..]),
                        "missing error"
                    );
                }
            }
        }
    }

    /// Larger run than `decoder_matches_reference`. Also puts errors in bursts and in the
    /// parity bytes, and uses blocks with all-zero and all-0xff message bytes.
    #[test]
    fn decoder_matches_reference_stress() {
        let mut rng = Rng(7);
        for round in 0..3000 {
            let msg: Vec<u8> = match round % 3 {
                0 => vec![0; 223],
                1 => vec![0xff; 223],
                _ => (0..223).map(|_| rng.byte()).collect(),
            };
            let good = to_dual(&encode(&msg));
            let mut bad = good.clone();
            let count = (rng.next() % 22) as usize;
            let start = (rng.next() % 255) as usize;
            for i in 0..count {
                // bursts on odd rounds, scattered on even rounds
                let p = if round % 2 == 1 {
                    (start + i) % 255
                } else {
                    (rng.next() % 255) as usize
                };
                bad[p] ^= rng.nonzero_byte();
            }
            let got = crate::correct_message(&bad);
            let want = correct_message(&bad);
            assert_eq!(got.state, want.state, "round={round} count={count}");
            assert_eq!(got.message, want.message, "round={round} count={count}");
        }
    }

    /// Random data is almost never a valid block. Both decoders must agree on it too.
    #[test]
    fn decoder_matches_reference_on_random_input() {
        let mut rng = Rng(5);
        for _ in 0..200 {
            let bad: Vec<u8> = (0..255).map(|_| rng.byte()).collect();
            let got = crate::correct_message(&bad);
            let want = correct_message(&bad);
            assert_eq!(got.state, want.state);
            assert_eq!(got.message, want.message);
        }
    }

    #[test]
    fn decoder_matches_reference_on_bad_length() {
        for len in [0, 1, 254, 256, 300] {
            let bad = vec![0u8; len];
            let got = crate::correct_message(&bad);
            let want = correct_message(&bad);
            assert_eq!(got.state, want.state);
            assert_eq!(got.message, want.message);
        }
    }
}
