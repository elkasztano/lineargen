# Lineargen

`rand` compatible bit sequence generators
based on Galois linear feedback shift registers.

Due to the compatibility with `rand`, various kinds of
number sequences can be generated. One can also choose
elements from slices or shuffle them using the generated
bit sequence from the LFSR.

Note that LFSRs are extremely fast and easy to implement,
but their statistical properties might not always be the
best and they are definitely _not_ cryptographically
secure.

## Examples

Choose from elements in an array:

```rust
use rand::SeedableRng; // 0.8.5
use rand::seq::SliceRandom;
use lineargen::large::Linear128;

fn main() {
    let mut rng = Linear128::seed_from_u64(987654321);

    for _ in 0..100 { rng.clock(); }

    let my_data = ["foo", "bar", "baz", "qux"];

    // choose elements pseudorandomly
    for _ in 0..10 {
        println!("{}", my_data.choose(&mut rng).unwrap());
    }
}
```

Generate a sequence of `f32`:

```rust
use rand::prelude::*; // 0.8.5
use lineargen::Linear64;

fn main() {
    let mut rng = Linear64::seed_from_u64(0x5EED5EED5EED);

    for _ in 0..128 { rng.clock(); }

    for _ in 0..20 {
        let my_float: f32 = rng.gen();
        println!("{}", my_float);
    }
}

```

See how the LFSR actually works:

```rust
use rand_core::SeedableRng; // 0.6.4
use lineargen::Linear16;

fn main() {
    let mut rng = Linear16::seed_from_u64(1023);

    for _ in 0..50 {
        rng.clock();
        println!("{:016b}", rng.dump_state());
    }
}
```

## Reference

The LFSR taps were taken from:
[https://www.physics.otago.ac.nz/reports/electronics/ETR2012-1.pdf](https://www.physics.otago.ac.nz/reports/electronics/ETR2012-1.pdf).
