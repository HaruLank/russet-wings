# Russet Wings

`russet-wings` is a Rust code generator for Idris 2, which aims for good interoperability with the Rust's ecosystem and complete support for all Idris 2 features. `russet-wings` is in its early stages, please feel free to ask anything you are interested in.

## Quickstart

```shell
# Make sure you also installed the Idris 2 API.
$ idris2 --build russet-wings.ipkg
$ ./build/exec/russet-wings --cg rust ./tests/hello.idr -o ./tests/hello.rs
# Make sure you installed the Rust compiler.
$ rustc ./tests/hello.rs -o ./tests/hello && ./tests/hello
```
