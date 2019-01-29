#![feature(rustc_attrs)]

#[rustc_symbol_name] //~ ERROR symbol-name(_RNaCs4fqI2P2rA04_5basic4main)
#[rustc_def_path] //~ ERROR def-path(main)
fn main() {
}
