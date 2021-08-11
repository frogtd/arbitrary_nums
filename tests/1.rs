use std::convert::TryInto;

use arbitrary_nums::*;

#[test]
fn it_adds_two() {
    assert_eq!(
        4,
        u4::new_infallible(2)
            .wrapping_add(u4::new_infallible(2))
            .as_byte()
    );
}


#[test]
fn to_ne_bytes() {
    let num = u4::new(9).unwrap();
    assert_eq!(num.to_ne_bytes(), [9]);
}

#[test]
fn count_zeros() {
    let num = u4::new(0xF).unwrap();
    assert_eq!(num.count_zeros(), 0);
    let num = u4::new(0x0).unwrap();
    assert_eq!(num.count_zeros(), 4);
}

#[test]
fn next_power_of_two() {
    let num: u4 = u4::new(7).unwrap();
    assert_eq!(num.next_power_of_two().as_byte(), 8);
}

#[test]
fn rotate() {
    let num = u4::new(0b0011).unwrap();
    assert_eq!(num.rotate_right(1).as_byte(), 0b1001);
    assert_eq!(num.rotate_right(2).as_byte(), 0b1100);
    assert_eq!(num.rotate_right(3).as_byte(), 0b0110);
    assert_eq!(num.rotate_right(4).as_byte(), 0b0011);

    assert_eq!(num.rotate_left(1).as_byte(), 0b0110);
    assert_eq!(num.rotate_left(2).as_byte(), 0b1100);
    assert_eq!(num.rotate_left(3).as_byte(), 0b1001);
    assert_eq!(num.rotate_left(4).as_byte(), 0b0011);
}

#[test]
#[should_panic]
fn next_power_of_two_panic() {
    let num: u4 = u4::new(15).unwrap();
    if cfg!(debug_assertions) {
        num.next_power_of_two().as_byte();
    } else {
        // this is asserting that they are equal but this test is `should_panic`
        assert_ne!(num.next_power_of_two().as_byte(), 0);
    }
}

#[test] 
fn add() {
    let num1: u4 = u4::new(6).unwrap();
    let num2: u4 = u4::new(2).unwrap();
    let _ = num1 + num2;
    let num1 = &num1;
    let _ = num1 + num2;
    let _ = num2 + num1;
    let _ = num1 + num1;
}

#[test]
fn from_str_radix() {
    assert_eq!(u4::from_str_radix("A", 15), Ok(10.try_into().unwrap()));
}