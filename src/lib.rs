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

fn correct_errata(input: &[u8], synd: &[u8], errpos: &[i32]) -> Result<Vec<u8>, &'static str> {
    let mut coef_pos = vec![0i32; errpos.len()];
    for (i, p) in errpos.iter().enumerate() {
        coef_pos[i] = input.len() as i32 - 1 - p;
    }

    let errloc = find_errata_locator(&coef_pos[..]);
    let mut rev_synd = synd.to_owned();
    rev_synd.reverse();
    let mut erreval = find_error_evaluator(&rev_synd, &errloc, errloc.len() as i32 - 1);
    erreval.reverse();

    let mut x = vec![0u8; coef_pos.len()];
    for (i, p) in coef_pos.iter().enumerate() {
        x[i] = gf::pow(GEN as u8, -(N as i32 - p));
    }

    let mut e = vec![0u8; input.len()];
    for (i, xi) in x.iter().enumerate() {
        let xi_inv = gf::inv(*xi);
        let mut errloc_prime_tmp: Vec<u8> = Vec::new();
        for j in 0..x.len() {
            if j != i {
                errloc_prime_tmp.push(1 ^ gf::mult(xi_inv, x[j]));
            }
        }
        let mut errloc_prime = 1u8;
        for c in errloc_prime_tmp.iter() {
            errloc_prime = gf::mult(errloc_prime, *c);
        }

        let mut erreval_rev = erreval.to_owned();
        erreval_rev.reverse();
        let mut y = gf::poly_eval(&erreval_rev, xi_inv);
        y = gf::mult(gf::pow(*xi, 1 - FCR), y);

        if errloc_prime == 0 {
            return Err("failed to find error magnitude");
        }

        e[errpos[i] as usize] = gf::div(y, errloc_prime);
    }

    let zult = &gf::poly_add(&input, &e);
    Ok(zult.to_vec())
}

fn find_errata_locator(errpos: &[i32]) -> Vec<u8> {
    let mut errloc = vec![1u8];
    for p in errpos.iter() {
        let x = &[gf::pow(GEN as u8, *p), 0];
        let y = gf::poly_add(&[1u8], x);
        errloc = gf::poly_mult(&errloc, &y);
    }
    errloc
}

fn find_error_evaluator(synd: &[u8], errloc: &[u8], n: i32) -> Vec<u8> {
    let mut divisor: Vec<u8> = vec![0u8; n as usize + 2];
    divisor[0] = 1;
    let (_, rem) = gf::poly_div(&gf::poly_mult(&synd, &errloc), &divisor);
    rem
}

fn find_errors(errloc: &[u8]) -> Vec<i32> {
    let num_errs = errloc.len() - 1;
    let mut errpos: Vec<i32> = Vec::with_capacity(num_errs);
    let n = N as i32;
    for i in 0..n {
        if gf::poly_eval(errloc, gf::pow(GEN, i as i32)) == 0 {
            errpos.push(N as i32 - 1 - i);
        }
    }
    errpos
}

fn find_error_locator(synd: &[u8], parity_len: usize) -> Vec<u8> {
    let mut errloc = vec![1u8];
    let mut oldloc = vec![1u8];
    let mut synd_shift = 0;
    if synd.len() > parity_len {
        synd_shift = synd.len() - parity_len;
    }
    for i in 0..parity_len {
        let k = i as usize + synd_shift;
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

    while errloc.len() > 0 && errloc[0] == 0 {
        errloc = errloc[1..].to_vec();
    }

    errloc
}

fn forney_syndromes(synd: &[u8], pos: &[i32], nmess: i32) -> Vec<u8> {
    let mut erase_pos_rev = vec![0i32; pos.len()];
    for (i, p) in pos.iter().enumerate() {
        erase_pos_rev[i] = nmess - 1 - p;
    }
    let mut fsynd: Vec<u8> = Vec::with_capacity(synd.len() - 1);
    fsynd.extend_from_slice(&synd[1..]);
    for i in 0..pos.len() {
        let x = gf::pow(GEN as u8, erase_pos_rev[i]);
        for j in 0..fsynd.len() - 1 {
            fsynd[j] = gf::mult(fsynd[j], x) ^ fsynd[j + 1];
        }
    }
    fsynd
}

fn calc_syndromes(input: &[u8], parity_len: usize) -> Vec<u8> {
    let mut synd: Vec<u8> = vec![0u8; parity_len + 1];
    for i in 0..parity_len {
        let p = gf::pow(GEN, i as i32 + FCR);
        synd[i + 1] = gf::poly_eval(&input, p);
    }
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
    let input = input.to_vec();
    if input.len() != N as usize {
        return Block {
            state: RSState::Uncorrectable("invalid input".to_owned()),
            message: None,
        };
    }
    let out = dual_basis::to_conv(&input).clone();

    let synd = calc_syndromes(&out, PARITY_LEN);
    let max = synd.iter().max().unwrap();
    // if there are no non-zero elements there are no errors
    if *max == 0 {
        return Block {
            state: RSState::Ok,
            message: Some(input),
        };
    }

    let fsynd = forney_syndromes(&synd, &[], out.len() as i32);
    let errloc = find_error_locator(&fsynd[..], PARITY_LEN);

    let num_errs = errloc.len() - 1;
    if num_errs * 2 > PARITY_LEN {
        return Block {
            state: RSState::Uncorrectable(format!(
                "too many errors to correct; expected no more than {:?}, found {:?}",
                PARITY_LEN / 2,
                num_errs
            ))
            .to_owned(),
            message: None,
        };
    }

    let mut errloc_rev = errloc.clone();
    errloc_rev.reverse();
    let errpos = find_errors(&errloc_rev[..]);
    if errpos.len() != num_errs {
        return Block {
            state: RSState::Uncorrectable(
                format!(
                    "failed to generate error positions; expected {} postions, got {}",
                    num_errs,
                    errpos.len()
                )
                .to_owned(),
            ),
            message: None,
        };
    }

    let out = match correct_errata(&out, &synd, &errpos) {
        Err(err) => {
            return Block {
                state: RSState::Uncorrectable(err.to_owned()),
                message: None,
            }
        }
        Ok(block) => block,
    };

    let synd = calc_syndromes(&out, PARITY_LEN);
    if *synd.iter().max().unwrap() > 0 {
        return Block {
            state: RSState::Uncorrectable("failed to correct all errors".to_owned()),
            message: None,
        };
    }

    Block {
        state: RSState::Corrected(errloc.len() as i32 - 1),
        message: Some(dual_basis::to_dual(&out)),
    }
}

/// Return true if the input code block contains 1 or more errors.
pub fn has_errors(msg: &[u8]) -> bool {
    let msg = dual_basis::to_conv(msg);
    let mut x = 0;
    for i in calc_syndromes(&msg[..], PARITY_LEN) {
        if i > x {
            x = i;
        }
    }
    x != 0
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
