#[macro_export]
macro_rules! assert_let {
    ($lhs:pat = $rhs:expr) => {
        let $lhs = $rhs
        else {
            panic!("assert_let failed: {:?}", $rhs);
        };
    };
}
