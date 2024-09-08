//! # Lineargen
//!
//! `rand` compatible pseudorandom generators based on
//! linear feedback shift registers (LFSR).
//!
//! Bit sequence generators of that type are extremely fast
//! and have a small memory footprint. However, they might
//! not always have ideal statistical properties.
//!
//! Do __not__ use them for cryptographical purposes.

use rand_core::impls::fill_bytes_via_next;
use rand_core::{Error, RngCore, SeedableRng};

pub mod large;

/// 16-bit Galois linear feedback shift register.
/// This generator has an extremely short period
/// of _65535_.
///
/// # Example
/// ```
/// use rand_core::{SeedableRng, RngCore};
/// use lineargen::Linear16;
///
/// let mut rng = Linear16::seed_from_u64(1234567);
/// for _ in 0..100 { rng.next_u32(); }
///
/// assert_eq!(1407506474, rng.next_u32());
/// ```
pub struct Linear16 {
    s: u16,
}

/// 32-bit Galois linear feedback shift register.
/// Period length is _2<sup>32</sup>-1_.
///
/// # Example
/// ```
/// use rand_core::{SeedableRng, RngCore};
/// use lineargen::Linear32;
///
/// let mut rng = Linear32::seed_from_u64(987654);
/// for _ in 0..50 { rng.next_u64(); }
///
/// assert_eq!(0x9F040BC97563A834, rng.next_u64());
/// ```
pub struct Linear32 {
    s: u32,
}

/// 64-bit Galois linear feedback shift register.
/// Period length is _2<sup>64</sup>-1_.
///
/// # Example
/// ```
/// use rand_core::{SeedableRng, RngCore};
/// use lineargen::Linear64;
///
/// let mut rng = Linear64::seed_from_u64(987654);
/// for _ in 0..100 { rng.next_u64(); }
///
/// assert_eq!(0x266D2F296761A84C, rng.next_u64());
/// ```
pub struct Linear64 {
    s: u64,
}

macro_rules! impl_linear {
    ($t:ty) => {
        fn get_bit(&mut self) -> u8 {
            let output = self.s as u8 & 1u8;
            self.clock();
            output
        }

        fn get_bit_rev(&mut self) -> u8 {
            let shift = std::mem::size_of::<$t>() * 8 - 1;
            let output = (self.s >> shift) as u8 & 1u8;
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

        /// Returns the current state of the LFSR.
        pub fn dump_state(&self) -> $t {
            self.s
        }

        /// Reverses the bits of the state, i.e.
        /// the least significant bit becomes the most
        /// significant one and vice versa.
        pub fn reverse_state(&mut self) {
            self.s = self.s.reverse_bits();
        }

        /// Negates the bits of the state.
        pub fn inverse_state(&mut self) {
            self.s = !self.s;
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
    };
}

impl Linear16 {
    /// Clock the LFSR once without generating a number.
    pub fn clock(&mut self) {
        let lsb = self.s & 1u16;
        self.s >>= 1;
        if lsb == 1 {
            // taps at bits 16, 14, 13, 11
            self.s ^= 0b1011_0100_0000_0000;
        }
    }

    /// Clock the LFSR in reverse.
    pub fn clock_rev(&mut self) {
        let msb = self.s >> 15;
        self.s <<= 1;
        if msb == 1 {
            // reverse taps
            self.s ^= 0b0000_0000_0010_1101;
        }
    }

    impl_linear!(u16);
}

impl Linear32 {
    /// Clock the LFSR once without generating a number.
    pub fn clock(&mut self) {
        let lsb = self.s & 1u32;
        self.s >>= 1;
        if lsb == 1 {
            // taps at bits 32, 30, 26, 25
            self.s ^= 0b1010_0011_0000_0000_0000_0000_0000_0000;
        }
    }

    /// Clock the LFSR in reverse.
    pub fn clock_rev(&mut self) {
        let msb = self.s >> 31;
        self.s <<= 1;
        if msb == 1 {
            // reverse taps
            self.s ^= 0b0000_0000_0000_0000_0000_0000_1100_0101;
        }
    }

    impl_linear!(u32);
}

impl Linear64 {
    /// Clock the LFSR once without generating a number.
    pub fn clock(&mut self) {
        let lsb = self.s & 1u64;
        self.s >>= 1;
        if lsb == 1 {
            // taps at bits 64, 63, 61, 60
            self.s ^= 0xD800000000000000;
        }
    }

    /// Clock the LFSR in reverse.
    pub fn clock_rev(&mut self) {
        let msb = self.s >> 63;
        self.s <<= 1;
        if msb == 1 {
            // reverse taps
            self.s ^= 0x000000000000001B;
        }
    }

    impl_linear!(u64);
}

macro_rules! impl_core {
    ($name:ident) => {
        impl RngCore for $name {
            fn next_u32(&mut self) -> u32 {
                self.get_32bits()
            }

            fn next_u64(&mut self) -> u64 {
                self.get_64bits()
            }

            fn fill_bytes(&mut self, dest: &mut [u8]) {
                fill_bytes_via_next(self, dest);
            }

            fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
                self.fill_bytes(dest);
                Ok(())
            }
        }
    };
}

pub(crate) use impl_core;

impl_core!(Linear16);
impl_core!(Linear32);
impl_core!(Linear64);

macro_rules! impl_seedable {
    ($name:ident, $n:expr, $t:ty) => {
        impl SeedableRng for $name {
            type Seed = [u8; $n];

            fn from_seed(seed: [u8; $n]) -> Self {
                let mut all_zero = true;
                for i in 0..$n {
                    if seed[i] != 0 {
                        all_zero = false;
                        break;
                    }
                }
                if all_zero {
                    return Self { s: <$t>::MAX };
                }

                let mut output: $t = 0;
                for i in 0..$n {
                    output |= (seed[i] as $t) << (i * 8);
                }
                Self { s: output }
            }

            fn seed_from_u64(seed: u64) -> Self {
                let output = seed as $t;
                if output == 0 {
                    return Self { s: <$t>::MAX };
                }
                Self { s: output }
            }
        }
    };
}

pub(crate) use impl_seedable;

impl_seedable!(Linear16, 2, u16);
impl_seedable!(Linear32, 4, u32);
impl_seedable!(Linear64, 8, u64);
