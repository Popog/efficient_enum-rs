# Efficient Enum

[![Version](https://img.shields.io/crates/v/efficient_enum.svg)](https://crates.io/crates/efficient_enum)
![License](https://img.shields.io/crates/l/efficient_enum.svg)
[![Downloads](https://img.shields.io/crates/d/efficient_enum.svg)](https://crates.io/crates/efficient_enum)

This crate aims to bring some space-efficient tagged unions similar to `enum`s. Instead of adding an extra bit, a bit of the existing structure is used. Users can customize which bit should be used at compile time.

For the moment, only `EfficientOption` and `EfficientOptionTuple` are provided, due to Rust's lack of a `const fn` version of `size_of`, which is needed to make size guarantees.

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
