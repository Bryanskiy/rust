// WIP on library/core/src/ptr/non_null.rs:765:9

use std::hash;

struct NonNull {
    data: u8
}

impl hash::Hash for NonNull {
    // fn hash<H: hash::Hasher>(&self, state: &mut H) {
    //     self.data.hash(state)
    // }
    override hash { self.data }
}

fn main() {}
