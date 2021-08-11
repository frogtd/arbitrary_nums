# arbitrary_nums
arbitrary_nums is a crate for arbitrary sized numbers, with niches.

## Usage

```rust
use arbitrary_nums::u4;

let num1: u4 = u4::new(6).unwrap();
let num2: u4 = u4::new(2).unwrap();
num1 + num2;
```
You can use them just like regular numbers!

## `#![no_std]`

This crate supports `no_std`, just disable the default features. (All it removes is `Error` impls)