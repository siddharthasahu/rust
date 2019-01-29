#![feature(rustc_attrs)]
#![allow(dead_code)]

mod foo {
    pub struct Foo { x: u32 }

    impl Foo {
        #[rustc_symbol_name]
        //~^ ERROR symbol-name(_RNpMNdCs4fqI2P2rA04_5impl13fooNnB2_3Foo3bar)
        #[rustc_def_path] //~ ERROR def-path(foo::Foo::bar)
        fn bar() { }
    }
}

mod bar {
    use foo::Foo;

    impl Foo {
        #[rustc_symbol_name]
        //~^ ERROR symbol-name(_RNxMNoCs4fqI2P2rA04_5impl13barNnNdB4_3foo3Foo3baz)
        #[rustc_def_path] //~ ERROR def-path(bar::<impl foo::Foo>::baz)
        fn baz() { }
    }
}

fn main() {
}
