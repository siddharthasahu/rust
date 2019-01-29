// compile-flags: -C no-prepopulate-passes

pub fn main() {

    // We want to make sure that closures get 'internal' linkage instead of
    // 'weak_odr' when they are not shared between codegen units
    // CHECK-LABEL: ; internalize_closures::main::{closure#0}
    // CHECK-NEXT: ; Function Attrs:
    // CHECK-NEXT: define internal
    let c = |x:i32| { x + 1 };
    let _ = c(1);
}
