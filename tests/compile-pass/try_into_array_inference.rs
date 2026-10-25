use std::array::TryFromSliceError;
use std::convert::TryInto;

fn consume_array_result(_: Result<[u8; size_of::<u16>()], TryFromSliceError>) {}

fn inferred_array(bytes: &[u8]) {
    let two_bytes = bytes[..2].try_into();
    consume_array_result(two_bytes);
}

fn main() {
    inferred_array(&[1, 2]);
}
