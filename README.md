# kv-pairs

Generic key-value pair builder for API params and form data.

This crate provides [`KVPairs`], an ordered collection of key-value pairs, whose values can be either borrowed or owned, that can be used as HTTP query strings or form bodies. The [`kv_pairs!`] macro can be used to build `KVPairs` instances with a literal-like syntax.

`KVPairs` accepts values that implement [`IntoValue`], including most primitive and standard library types like `&str`, `String`, `bool`, and common integer types. The `impl_into_value_by_*` macros can be used to implement [`IntoValue`] for more types.

`KVPairs` also accepts values that implement [`IntoValues`], to insert 0, 1, or more values for a single key. This is useful for optional or multi-value parameters. The keys are **never** automatically suffixed with `[]` when inserting values via [`IntoValues`].

## Example

```rust
use kv_pairs::{kv_pairs, KVPairs};

let params = kv_pairs![
    "mode" => "day",
    "page" => 1_u32,
];
assert_eq!(params.content.len(), 2);
```

## no_std

This crate supports `no_std` with the `alloc` crate. Disable the default `std` feature:

```toml
kv-pairs = { version = "0.1", default-features = false }
```

## License

MIT
