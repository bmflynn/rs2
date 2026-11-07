//! Reed-Solomon Forward Error Correction for spacecraft data conforming to [CCSDS](https://public.ccsds.org)
//! TM SYNCHRONIZATION AND CHANNEL CODING ([131.0-B-5](https://public.ccsds.org/Pubs/131x0b5.pdf).
//!
//! This is only intended to perform RS as documented in the CCSDS document linked above. It is not
//! a general purpose Reed-Solomon FEC implementation.
//!
//! This has been ported and adopted from the Python code found in the excelent article
//! [Reed-Solomon Codes for Coders](https://en.wikiversity.org/wiki/Reed%E2%80%93Solomon_codes_for_coders).
pub mod dual_basis;
pub mod gf;
#[cfg(test)]
mod reference;

/// Symbols per code word
pub const N: u8 = 255;
/// Bits per symbol
#[allow(unused)]
pub const J: u8 = 8;
/// Common irreducible primative polynomial x^8 + x^7 + x^2 + x + 1
#[allow(unused)]
pub const PRIM: i32 = 391;
/// Primative element: alpha 11
pub const GEN: u8 = 173;
/// First consecutive root in g(x): 128-E
pub const FCR: i32 = 112;
/// Number of bytes of parity for each message.
pub const PARITY_LEN: usize = 32;

/// Disposition of the RS process
#[derive(Debug, PartialEq, Clone)]
pub enum RSState {
    /// RS was performed and no errors were found
    Ok,
    /// RS was performed and the provided number of errors were successfully correct.
    Corrected(i32),
    /// RS was performed but the RS codeblock was not correctable, e.g., there were
    /// more errors than could be corrected.
    Uncorrectable(String),
    NotPerformed,
}

/// Largest number of symbol errors the code can correct.
const MAX_ERRORS: usize = PARITY_LEN / 2;

/// Capacity for the error locator polynomial in the Berlekamp-Massey loop. The length of
/// the polynomial is at most PARITY_LEN + 1.
const LOC_CAP: usize = PARITY_LEN + 2;

/// Result of a successful decode: where the errors are and what to XOR into them.
/// Positions are indexes into the block. Values are in conventional representation.
struct Errata {
    count: usize,
    pos: [u8; MAX_ERRORS],
    val: [u8; MAX_ERRORS],
}

impl Errata {
    /// Fix the errors in a dual basis block.
    fn apply(&self, block: &mut [u8]) {
        for i in 0..self.count {
            let p = self.pos[i] as usize;
            block[p] = dual_basis::dual_byte(dual_basis::conv_byte(block[p]) ^ self.val[i]);
        }
    }
}

/// Berlekamp-Massey. Returns the error locator, highest degree first, and its length.
/// `synd` are the syndromes, without the leading zero.
fn find_error_locator(synd: &[u8; PARITY_LEN]) -> ([u8; LOC_CAP], usize) {
    let mut errloc = [0u8; LOC_CAP];
    let mut oldloc = [0u8; LOC_CAP];
    errloc[0] = 1;
    oldloc[0] = 1;
    let mut el = 1;
    let mut ol = 1;
    for i in 0..PARITY_LEN {
        let mut delta = synd[i];
        for j in 1..el {
            delta ^= gf::mult(errloc[el - j - 1], synd[i - j]);
        }
        oldloc[ol] = 0;
        ol += 1;
        if delta != 0 {
            if ol > el {
                let mut newloc = [0u8; LOC_CAP];
                for k in 0..ol {
                    newloc[k] = gf::mult(oldloc[k], delta);
                }
                let dinv = gf::inv(delta);
                let mut newold = [0u8; LOC_CAP];
                for k in 0..el {
                    newold[k] = gf::mult(errloc[k], dinv);
                }
                let new_ol = el;
                errloc = newloc;
                el = ol;
                oldloc = newold;
                ol = new_ol;
            }
            // errloc += delta * oldloc, with the low degree ends lined up
            let l = el.max(ol);
            if l > el {
                errloc.copy_within(0..el, l - el);
                errloc[..l - el].fill(0);
            }
            for k in 0..ol {
                errloc[l - ol + k] ^= gf::mult(oldloc[k], delta);
            }
            el = l;
        }
    }

    // drop leading zeros
    let start = errloc[..el].iter().position(|c| *c != 0).unwrap_or(el);
    errloc.copy_within(start..el, 0);
    (errloc, el - start)
}

/// Chien search. `errloc` is the locator, highest degree first. Finds positions where the
/// reversed polynomial is zero. Stops as soon as `want` roots are found, because a
/// polynomial cannot have more roots than its degree. Returns the positions and how many
/// were found.
fn find_errors(errloc: &[u8], want: usize) -> ([u8; MAX_ERRORS], usize) {
    // The reversed polynomial evaluated at x is sum(errloc[e] * x^e). At x = alpha^i that is
    // sum(errloc[e] * alpha^(i*e)).
    // Keep each term and multiply it by alpha^e for the next i.
    let len = errloc.len();
    let mut term = [0u8; LOC_CAP];
    let mut step = [0u8; LOC_CAP];
    for e in 0..len {
        term[e] = errloc[e];
        step[e] = gf::pow(GEN, e as i32);
    }
    let mut pos = [0u8; MAX_ERRORS];
    let mut count = 0;
    for i in 0..N as usize {
        let mut sum = 0u8;
        for e in 0..len {
            sum ^= term[e];
            term[e] = gf::mult(term[e], step[e]);
        }
        if sum == 0 {
            if count < MAX_ERRORS {
                pos[count] = (N as usize - 1 - i) as u8;
            }
            count += 1;
            if count == want {
                break;
            }
        }
    }
    (pos, count)
}

/// Forney algorithm. Returns the error values for the given positions, or an error text.
fn find_error_values(
    synd: &[u8; PARITY_LEN],
    pos: &[u8],
) -> Result<[u8; MAX_ERRORS], &'static str> {
    let n = pos.len();
    let mut coef = [0i32; MAX_ERRORS];
    for i in 0..n {
        coef[i] = N as i32 - 1 - pos[i] as i32;
    }

    // errata locator: product of (a_i * x + 1), highest degree first, length n+1
    let mut loc = [0u8; MAX_ERRORS + 1];
    loc[0] = 1;
    for i in 0..n {
        let a = gf::pow(GEN, coef[i]);
        let mut next = [0u8; MAX_ERRORS + 1];
        for k in 0..=i {
            next[k] ^= gf::mult(loc[k], a);
            next[k + 1] ^= loc[k];
        }
        loc = next;
    }
    let l = n + 1;

    // error evaluator: the last l coefficients of reversed_syndromes * loc.
    // reversed_syndromes[a] = synd[31 - a] for a < 32, and 0 for a = 32.
    let mut eval = [0u8; MAX_ERRORS + 1];
    for u in 0..l {
        let mut v = 0u8;
        for b in (u + 1)..l {
            v ^= gf::mult(synd[b - u - 1], loc[b]);
        }
        eval[u] = v;
    }

    let mut x = [0u8; MAX_ERRORS];
    for i in 0..n {
        x[i] = gf::pow(GEN, -(N as i32 - coef[i]));
    }

    let mut vals = [0u8; MAX_ERRORS];
    for i in 0..n {
        let xi = x[i];
        let xi_inv = gf::inv(xi);
        let mut prime = 1u8;
        for j in 0..n {
            if j != i {
                prime = gf::mult(prime, 1 ^ gf::mult(xi_inv, x[j]));
            }
        }
        let mut y = eval[0];
        for c in &eval[1..l] {
            y = gf::mult(y, xi_inv) ^ *c;
        }
        y = gf::mult(gf::pow(xi, 1 - FCR), y);

        if prime == 0 {
            return Err("failed to find error magnitude");
        }
        vals[i] = gf::div(y, prime);
    }
    Ok(vals)
}

/// True if XORing the error values into the block makes all syndromes zero.
///
/// Syndromes are linear in the block. Adding value v at a position with degree c changes
/// syndrome k by v * (alpha^(FCR+k))^c. So the new syndromes come from the old ones and the
/// errors alone, with no pass over the 255 bytes.
fn errata_clears_syndromes(synd: &[u8; PARITY_LEN], pos: &[u8], val: &[u8]) -> bool {
    let mut s = *synd;
    for (p, v) in pos.iter().zip(val) {
        let c = N as i32 - 1 - *p as i32;
        let a = gf::pow(GEN, c);
        let mut cur = gf::pow(GEN, FCR * c);
        for sk in s.iter_mut() {
            *sk ^= gf::mult(*v, cur);
            cur = gf::mult(cur, a);
        }
    }
    s.iter().all(|x| *x == 0)
}

/// Error path. `synd` are the syndromes of a block, and at least one of them is not zero.
fn find_errata(synd: &[u8; PARITY_LEN]) -> Result<Errata, String> {
    let (errloc, el) = find_error_locator(synd);

    let num_errs = el - 1;
    if num_errs * 2 > PARITY_LEN {
        return Err(format!(
            "too many errors to correct; expected no more than {:?}, found {:?}",
            PARITY_LEN / 2,
            num_errs
        ));
    }

    let (pos, count) = find_errors(&errloc[..el], num_errs);
    if count != num_errs {
        return Err(format!(
            "failed to generate error positions; expected {} postions, got {}",
            num_errs, count
        ));
    }

    let val = find_error_values(synd, &pos[..count]).map_err(|e| e.to_owned())?;

    if !errata_clears_syndromes(synd, &pos[..count], &val[..count]) {
        return Err("failed to correct all errors".to_owned());
    }
    Ok(Errata { count, pos, val })
}

/// Multiplication tables for the syndrome roots. `tables[k][y] = y * GEN^(FCR+k)`.
/// Built once. 32 * 256 = 8 KB.
fn root_tables() -> &'static [[u8; 256]; PARITY_LEN] {
    static TABLES: std::sync::OnceLock<[[u8; 256]; PARITY_LEN]> = std::sync::OnceLock::new();
    TABLES.get_or_init(|| {
        let mut t = [[0u8; 256]; PARITY_LEN];
        for (k, row) in t.iter_mut().enumerate() {
            let root = gf::pow(GEN, k as i32 + FCR);
            for (y, v) in row.iter_mut().enumerate() {
                *v = gf::mult(y as u8, root);
            }
        }
        t
    })
}

/// Evaluate the input polynomial at all [PARITY_LEN] roots in one pass. The 32 Horner
/// chains do not depend on each other, so the CPU can run them at the same time.
fn syndromes_core(input: impl Iterator<Item = u8>) -> [u8; PARITY_LEN] {
    let tables = root_tables();
    let mut s = [0u8; PARITY_LEN];
    for b in input {
        for k in 0..PARITY_LEN {
            s[k] = tables[k][s[k] as usize] ^ b;
        }
    }
    s
}

/// Syndromes of a dual basis block. Element 0 of the result is the first syndrome.
fn syndromes_dual(input: &[u8]) -> [u8; PARITY_LEN] {
    syndromes_core(input.iter().map(|b| dual_basis::conv_byte(*b)))
}

/// Syndromes of a conventional basis block, with a leading zero element.
#[cfg(test)]
fn calc_syndromes(input: &[u8], parity_len: usize) -> Vec<u8> {
    assert!(parity_len <= PARITY_LEN);
    let mut synd: Vec<u8> = vec![0u8; parity_len + 1];
    let s = syndromes_core(input.iter().copied());
    synd[1..].copy_from_slice(&s[..parity_len]);
    synd
}

pub struct Block {
    /// Resuting state of the RS process for all contained RS messages.
    pub state: RSState,
    /// The checked codeblock without the RS check symbols.
    pub message: Option<Vec<u8>>,
}

/// Correct a Reed-Solomon 255 byte code block, where the last [PARITY_LEN] bytes are
/// the parity/check bytes. The code block is also assumed to be in dual basis
/// representation.
///
/// The returned [Block::message} will contain the corrected message iff the state is
/// [RSState::Corrected]. Otherwise it will be None.
///
/// The state will be [RSState::Uncorrectable] if there are more errors than can be
/// corrected or if an algorithm failure occurs.
pub fn correct_message(input: &[u8]) -> Block {
    if input.len() != N as usize {
        return Block {
            state: RSState::Uncorrectable("invalid input".to_owned()),
            message: None,
        };
    }

    // Fast path: syndromes straight from the dual basis input. No conversion copy.
    let s = syndromes_dual(input);
    // if there are no non-zero elements there are no errors
    if s.iter().all(|x| *x == 0) {
        return Block {
            state: RSState::Ok,
            message: Some(input.to_vec()),
        };
    }
    match find_errata(&s) {
        Err(msg) => Block {
            state: RSState::Uncorrectable(msg),
            message: None,
        },
        Ok(errata) => {
            let mut out = input.to_vec();
            errata.apply(&mut out);
            Block {
                state: RSState::Corrected(errata.count as i32),
                message: Some(out),
            }
        }
    }
}

/// Correct a block in place. The buffer must be a 255 byte code block in dual basis
/// representation, the same as for [correct_message].
///
/// This does not allocate unless the block is uncorrectable (the state then holds a
/// message). On [RSState::Corrected] the buffer holds the corrected block (parity bytes
/// included, same as [Block::message]). In every other state the buffer is not changed.
pub fn correct_in_place(buf: &mut [u8; N as usize]) -> RSState {
    let s = syndromes_dual(buf);
    if s.iter().all(|x| *x == 0) {
        return RSState::Ok;
    }
    match find_errata(&s) {
        Err(msg) => RSState::Uncorrectable(msg),
        Ok(errata) => {
            errata.apply(buf);
            RSState::Corrected(errata.count as i32)
        }
    }
}

/// Return true if the input code block contains 1 or more errors.
pub fn has_errors(msg: &[u8]) -> bool {
    syndromes_dual(msg).iter().any(|x| *x != 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    // RS message, no pn
    const FIXTURE_MSG: &[u8; 255] = &[
        0x67, 0xc4, 0x6b, 0xa7, 0x3e, 0xbe, 0x4c, 0x33, 0x6c, 0xb2, 0x23, 0x3a, 0x74, 0x06, 0x2b,
        0x18, 0xab, 0xb8, 0x09, 0xe6, 0x7d, 0xaf, 0x5d, 0xe5, 0xdf, 0x76, 0x25, 0x3f, 0xb9, 0x14,
        0xee, 0xec, 0xd1, 0xa3, 0x39, 0x5f, 0x38, 0x68, 0xf0, 0x26, 0xa6, 0x8a, 0xcb, 0x09, 0xaf,
        0x4e, 0xf8, 0x93, 0xf7, 0x45, 0x4b, 0x0d, 0xa9, 0xb8, 0x74, 0x0e, 0xf3, 0xc7, 0xed, 0x6e,
        0xa3, 0x0f, 0xf6, 0x79, 0x94, 0x16, 0xe2, 0x7f, 0xad, 0x91, 0x91, 0x04, 0xac, 0xa4, 0xae,
        0xb4, 0x51, 0x76, 0x2f, 0x62, 0x03, 0x5e, 0xa1, 0xe5, 0x5c, 0x45, 0xf8, 0x1f, 0x7a, 0x7b,
        0xe8, 0x35, 0xd8, 0xcc, 0x51, 0x0e, 0xae, 0x3a, 0x2a, 0x64, 0x1d, 0x03, 0x10, 0xcd, 0x18,
        0xe6, 0x7f, 0xef, 0xba, 0xd9, 0xe8, 0x98, 0x47, 0x82, 0x9c, 0xa1, 0x58, 0x47, 0x25, 0xdf,
        0x41, 0xd2, 0x01, 0x62, 0x3c, 0x24, 0x88, 0x90, 0xe9, 0xd7, 0x38, 0x1b, 0xa0, 0xa2, 0xb4,
        0x23, 0xea, 0x7e, 0x58, 0x0d, 0xf4, 0x61, 0x24, 0x14, 0xb0, 0x41, 0x90, 0x0c, 0xb7, 0xbb,
        0x5c, 0x59, 0x1b, 0xc6, 0x69, 0x24, 0x0f, 0xb6, 0x0e, 0x14, 0xa1, 0xb1, 0x8e, 0x48, 0x0f,
        0x17, 0x1d, 0xfb, 0x0f, 0x38, 0x42, 0xe3, 0x24, 0x58, 0xab, 0x82, 0xa8, 0xfd, 0xdf, 0xac,
        0x68, 0x93, 0x3d, 0x0d, 0x8f, 0x50, 0x52, 0x44, 0x6c, 0xba, 0xd3, 0x51, 0x99, 0x9c, 0x3e,
        0xad, 0xd5, 0xa8, 0xd7, 0x9d, 0xc7, 0x7f, 0x9f, 0xc9, 0x2a, 0xac, 0xe5, 0xc2, 0xcd, 0x9a,
        0x9b, 0xfa, 0x2d, 0x72, 0xab, 0x6b, 0xa4, 0x6b, 0x8b, 0x7d, 0xfa, 0x6c, 0x83, 0x63, 0x77,
        0x9f, 0x4e, 0x9a, 0x20, 0x35, 0xd2, 0x91, 0xce, 0xf4, 0x21, 0x1a, 0x97, 0x3c, 0x1a, 0x15,
        0x9d, 0xfc, 0x98, 0xba, 0x72, 0x1b, 0x9a, 0xa2, 0xe9, 0xc9, 0x46, 0x68, 0xce, 0xad, 0x27,
    ];

    #[test]
    fn test_calc_syndromes() {
        const EXPECTED: &[u8] = &[
            0x00, 0xb7, 0xd5, 0x62, 0x7b, 0xf5, 0xa0, 0x52, 0x91, 0xc1, 0xd2, 0x97, 0xd0, 0x40,
            0x68, 0x59, 0x0d, 0xcb, 0xc0, 0x84, 0x84, 0x68, 0xa6, 0xd9, 0x79, 0xf9, 0xad, 0x4c,
            0x81, 0x9f, 0x14, 0x2f, 0x78,
        ];

        let zult = calc_syndromes(FIXTURE_MSG, PARITY_LEN);

        for ((i, z), e) in zult.iter().enumerate().zip(EXPECTED.iter()) {
            assert_eq!(
                z, e,
                "not all elements equal: expected {}, got {} at index {}\n{:?}",
                e, z, i, zult
            );
        }
    }

    #[test]
    fn test_correct_message_noerrors() {
        let msg = FIXTURE_MSG.clone();

        assert!(!has_errors(&msg), "expected message not to have errors");

        let block = correct_message(&msg);

        assert_eq!(block.message.unwrap().len(), 255);
        assert_eq!(
            block.state,
            RSState::Ok,
            "correcting a message with no errors should be Ok"
        );
    }

    #[test]
    fn test_correct_message_introduced_errors() {
        let mut msg = FIXTURE_MSG.clone();

        // corrupt the message
        msg[0] = 0;
        msg[2] = 2;
        msg[4] = 2;
        msg[6] = 2;

        assert!(has_errors(&msg), "expected message to have errors");

        let block = correct_message(&msg);
        assert_eq!(block.message.unwrap().len(), 255);
        assert_eq!(block.state, RSState::Corrected(4));
    }

    #[test]
    fn test_correct_message2() {
        // block 80 message 0 from overpass_snpp_2017_7min.dat
        // This block contains errors and is already pn decoded
        let msg = vec![
            0x67, 0x4c, 0x00, 0xff, 0xff, 0x80, 0x02, 0xf8, 0x7f, 0x01, 0xf7, 0x4f, 0xb5, 0x65,
            0x14, 0x29, 0xfd, 0x68, 0x38, 0x9e, 0x6a, 0xca, 0x28, 0x53, 0xfa, 0xd0, 0x71, 0x3d,
            0xd4, 0x95, 0x50, 0xa6, 0xf4, 0xa0, 0xe2, 0x7b, 0xa9, 0x2a, 0xa1, 0x4c, 0xe9, 0x41,
            0xc5, 0xf6, 0x52, 0x54, 0x42, 0x99, 0xd2, 0x83, 0x8b, 0xed, 0xa5, 0xa8, 0x84, 0x33,
            0xa4, 0x06, 0x16, 0xdb, 0x4b, 0x51, 0x08, 0x66, 0x48, 0x0d, 0x2c, 0xb7, 0x97, 0xa2,
            0x10, 0xcd, 0x90, 0x1a, 0x59, 0x6e, 0x2e, 0x45, 0x21, 0x9b, 0x20, 0x35, 0xb2, 0xdd,
            0x5d, 0x8a, 0x43, 0x37, 0x40, 0x6b, 0x64, 0xba, 0xbb, 0x15, 0x87, 0x6f, 0x80, 0xd7,
            0xc9, 0x74, 0x77, 0x2b, 0x0f, 0xde, 0x01, 0xae, 0x92, 0xe8, 0xef, 0x57, 0x1e, 0xbd,
            0x03, 0x5c, 0x24, 0xd1, 0xdf, 0xaf, 0x3c, 0x7a, 0x07, 0xb8, 0x49, 0xa3, 0xbe, 0x5f,
            0x78, 0xf5, 0x0e, 0x70, 0x93, 0x46, 0x7d, 0xbf, 0xf1, 0xea, 0x1d, 0xe1, 0x27, 0x8d,
            0xfb, 0x7e, 0xe3, 0xd5, 0x3b, 0xc2, 0x4e, 0x1b, 0xf7, 0xfc, 0xc6, 0xaa, 0x76, 0x85,
            0x9d, 0x36, 0xee, 0xf9, 0x8c, 0x55, 0xec, 0x0b, 0x3a, 0x6c, 0xdc, 0xf3, 0x18, 0xab,
            0xd8, 0x17, 0x75, 0xd9, 0xb9, 0xe7, 0x31, 0x56, 0xb0, 0x2f, 0xeb, 0xb3, 0x73, 0xcf,
            0x62, 0xac, 0x60, 0x5e, 0xd6, 0x67, 0xe6, 0x9f, 0xc4, 0x58, 0xc0, 0xbc, 0xad, 0xce,
            0xcc, 0x3e, 0x88, 0xb1, 0x81, 0x79, 0x5b, 0x9c, 0x98, 0x7c, 0x11, 0x63, 0x02, 0xf2,
            0xb6, 0x39, 0x30, 0xf8, 0x22, 0xc7, 0x04, 0xe4, 0x6d, 0x72, 0x61, 0xf0, 0x44, 0x8f,
            0x09, 0xc8, 0xda, 0xe5, 0xc3, 0xe0, 0x89, 0x1f, 0x13, 0x91, 0xb4, 0xcb, 0x86, 0xc1,
            0x12, 0x3f, 0x26, 0x23, 0x69, 0x96, 0x0c, 0x82, 0x25, 0x7f, 0x4d, 0x47, 0xd3, 0x2d,
            0x19, 0x05, 0x4a,
        ];

        assert!(has_errors(&msg), "expected message to have errors");

        let block = correct_message(&msg);
        assert_eq!(block.message.unwrap().len(), 255);
        assert_eq!(block.state, RSState::Corrected(11));
    }
}
