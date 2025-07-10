# CHANGELOG

## 0.4.0 - 2025-07-10

* Upgrade to Rust 2024 edition
* **Breaking**: Require `Send` trait bound in addition to `Sync` for custom functions when `sync` feature is enabled:
  https://github.com/jmespath/jmespath.rs/pull/50
* Remove `lazy_static` and use `LazyLock`
* Fix panic on invalid number parsing:
  https://github.com/jmespath/jmespath.rs/pull/46
* Include `Cargo.lock` for the jmespath-cli project:
  https://github.com/jmespath/jmespath.rs/pull/48
* Update dependencies: bump libc from 0.2.139 to 0.2.155:
  https://github.com/jmespath/jmespath.rs/pull/52

## 0.3.0 - 2022-02-24

* Upgrade to Rust 2018 edition
* Remove usage of deprecated `try!` macro in favor of `?` operator
* Use `serde_json::Number` for improved number handling
* Fix serde error handling:
  https://github.com/jmespath/jmespath.rs/pull/34
* Make `Expression` implement `Clone`:
  https://github.com/jmespath/jmespath.rs/pull/29
* Update lazy_static to 1.x:
  https://github.com/jmespath/jmespath.rs/pull/30
* Reorganize project as a cargo workspace
* Remove unnecessary `unwrap()` calls throughout the codebase for better error handling
* Fix numerous clippy warnings
* Fix broken hyperlinks in documentation:
  https://github.com/jmespath/jmespath.rs/pull/37
* Run benchmarks on stable Rust (no longer require nightly)

## 0.2.0 - 2017-09-26

* Now works with Serde 1.0:
  https://github.com/jmespath/jmespath.rs/pull/24
* impl `Error` for `JmespathError`:
  https://github.com/jmespath/jmespath.rs/pull/22
* Removed parentheses around `Fn` to fix syntactic error:
  https://github.com/jmespath/jmespath.rs/pull/20

## 0.1.1 - 2017-01-07

* Now works on stable by placing specialization behind the `specialized`
  feature flag. https://github.com/jmespath/jmespath.rs/pull/19

## 0.1.0 - 2016-12-15

* First somewhat stable release.

## 0.0.1 - 2016-01-30

* Initial release.
