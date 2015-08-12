#![feature(test)]
#[cfg(test)]

extern crate jmespath;
extern crate test;
extern crate rustc_serialize;

use rustc_serialize::json::Json;
use test::Bencher;

#[bench]
fn bench_parsing_foo_bar_baz(b: &mut Bencher) {
    b.iter(|| jmespath::Expression::new("foo.bar.baz"));
}

#[bench]
fn bench_lexing_foo_bar_baz(b: &mut Bencher) {
    b.iter(|| for _ in jmespath::tokenize("foo.bar.baz") {});
}

#[bench]
fn bench_full_foo_bar_baz(b: &mut Bencher) {
    let json = Json::from_str("{\"foo\":{\"bar\":{\"baz\":true}}}").unwrap();
    b.iter(|| {
        let expr = jmespath::Expression::new("foo.bar.baz").unwrap();
        expr.search(json.clone()).unwrap();
    });
}

#[bench]
fn bench_full_or_branches(b: &mut Bencher) {
    let json = Json::from_str("{\"foo\":true}").unwrap();
    b.iter(|| {
        let expr = jmespath::Expression::new("bar || baz || bam || foo").unwrap();
        expr.search(json.clone()).unwrap();
    });
}

#[bench]
fn bench_expr_identifier(b: &mut Bencher) {
    let expr = "abcdefghijklmnopqrstuvwxyz";
    b.iter(|| jmespath::parse(expr));
}

#[bench]
fn bench_expr_subexpr(b: &mut Bencher) {
    let expr = "abcdefghijklmnopqrstuvwxyz.abcdefghijklmnopqrstuvwxyz";
    b.iter(|| jmespath::parse(expr));
}
