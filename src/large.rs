//! This module contains the `Linear128` LFSR with a
//! period of _2<sup>128</sup>-1_.

use crate::impl_core;
use rand_core::impls::fill_bytes_via_next;
use rand_core::le::read_u64_into;
use rand_core::{Error, RngCore, SeedableRng};

/// Galois LFSR with 128 bits of state.
///
/// # Example
/// ```
/// use rand_core::{SeedableRng, RngCore};
/// use lineargen::large::Linear128;
///
/// let mut rng = Linear128::seed_from_u64(4095);
/// for _ in 0..100 { rng.clock(); }
///
/// assert_eq!(816112992255, rng.next_u64());
/// ```
pub struct Linear128 {
    s: [u64; 2],
}

macro_rules! impl_large {
    ($nr: expr) => {
        fn get_bit(&mut self) -> u8 {
            let output = self.s[0] as u8 & 1u8;
            self.clock();
            output
        }

        fn get_bit_rev(&mut self) -> u8 {
            let output = (self.s[$nr - 1] >> 63) as u8;
            self.clock_rev();
            output
        }

        /// Returns `true` if the least significant bit
        /// is one, else returns `false`. The LFSR is
        /// clocked once.
        pub fn quick_bool(&mut self) -> bool {
            if self.get_bit() == 1 {
                true
            } else {
                false
            }
        }

        /// Returns `true` if the most significant bit is
        /// one, else returns `false`. The LFSR is
        /// clocked backwards.
        pub fn quick_bool_rev(&mut self) -> bool {
            if self.get_bit_rev() == 1 {
                true
            } else {
                false
            }
        }

        /// Generates a 32-bit unsigned integer.
        /// You might want to use `next_u32()` from `RngCore`
        /// instead.
        pub fn get_32bits(&mut self) -> u32 {
            let mut output = 0u32;
            for i in 0..32 {
                output |= (self.get_bit() as u32) << i;
            }
            output
        }

        /// Generates a 32-bit unsigned integer by clocking
        /// the LFSR in reverse (left shift).
        ///
        /// Note, that this will _not_ just return the numbers
        /// generated with `get_32bits()` in reverse order.
        pub fn get_32bits_rev(&mut self) -> u32 {
            let mut output = 0u32;
            for i in 0..32 {
                output |= (self.get_bit_rev() as u32) << (31 - i);
            }
            output
        }

        /// Generates a 64-bit unsigned integer.
        /// You might want to use `next_u64()` from `RngCore`
        /// instead.
        pub fn get_64bits(&mut self) -> u64 {
            let mut output = 0u64;
            for i in 0..64 {
                output |= (self.get_bit() as u64) << i;
            }
            output
        }

        /// Generates a 64-bit unsigned integer by clocking
        /// the LFSR in reverse (left shift).
        ///
        /// Note, that this will _not_ just return the numbers
        /// generated with `get_64bits()` in reverse order.
        pub fn get_64bits_rev(&mut self) -> u64 {
            let mut output = 0u64;
            for i in 0..64 {
                output |= (self.get_bit_rev() as u64) << (63 - i);
            }
            output
        }

        /// Reverse the bits of the state.
        pub fn reverse_state(&mut self) {
            let temp = self.s[0].reverse_bits();
            for i in 1..$nr {
                self.s[i - 1] = self.s[i].reverse_bits();
            }
            self.s[1] = temp;
        }

        /// Negate the bits of the state.
        pub fn inverse_state(&mut self) {
            for i in 0..$nr {
                self.s[i] = !self.s[i];
            }
        }

        /// Returns the current state of the LFSR.
        pub fn dump_state(&self) -> [u64; $nr] {
            self.s
        }
    };
}

impl Linear128 {
    /// Clock the LFSR without generating numbers.
    pub fn clock(&mut self) {
        let lsb = self.s[0] & 1;
        self.s[0] = self.s[0] >> 1 | self.s[1] << 63;
        self.s[1] >>= 1;
        if lsb == 1 {
            self.s[1] ^= 0xE100_0000_0000_0000;
        }
    }

    /// Clock the LFSR in reverse. Numbers are not generated.
    pub fn clock_rev(&mut self) {
        let msb = self.s[1] >> 63;
        self.s[1] = self.s[1] << 1 | self.s[0] >> 63;
        self.s[0] <<= 1;
        if msb == 1 {
            self.s[0] ^= 0x87;
        }
    }

    impl_large!(2);
}

impl_core!(Linear128);

macro_rules! impl_seedable_large {
    ($name: ident, $nr: expr) => {
        impl SeedableRng for $name {
            type Seed = [u8; $nr * 8];

            fn from_seed(seed: [u8; $nr * 8]) -> Self {
                let mut state = [0u64; $nr];
                read_u64_into(&seed, &mut state);

                if state == [0u64; $nr] {
                    for i in 0..$nr {
                        state[i] = u64::MAX;
                    }
                }
                Self { s: state }
            }

            fn seed_from_u64(seed: u64) -> Self {
                let mut state = [0u64; $nr];
                let mut flip = true;

                for x in state.iter_mut() {
                    if flip {
                        *x = seed;
                    } else {
                        *x = !seed;
                    }
                    flip = !flip;
                }
                Self { s: state }
            }
        }
    };
}

impl_seedable_large!(Linear128, 2);
