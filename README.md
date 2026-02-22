# kv-pairs

[![Crates.io](https://img.shields.io/crates/v/kv-pairs)](https://crates.io/crates/kv-pairs)
[![docs.rs](https://img.shields.io/docsrs/kv-pairs)](https://docs.rs/kv-pairs)
[![License: MIT](https://img.shields.io/crates/l/kv-pairs)](LICENSE)
[![CI](https://github.com/GeminiLab/kv-pairs/actions/workflows/ci.yml/badge.svg)](https://github.com/GeminiLab/kv-pairs/actions/workflows/ci.yml)

Key-value pair builder for API query strings and form data. Ordered, supports borrowed or owned values, and works with serde/reqwest.

## Example

### Basic usage

```rust
use kv_pairs::{kv_pairs, KVPairs};

let params = kv_pairs![
    "mode" => "day",
    "page" => 1_u32,
];
assert_eq!(params.content.len(), 2);
```

### Optional and multi-value params

```rust
use kv_pairs::{kv_pairs, KVPairs};

// Option: omit key when None
let p = kv_pairs![
    "q" => Some("search"),
    "filter" => None::<&str>,
];

// Multiple values for one key (e.g. tags[]=a&tags[]=b)
let p = kv_pairs![
    "tags[]" => ["a", "b"].as_slice(),
];
```

### no_std

Disable the default `std` feature to use this crate in `no_std` environments.

```toml
kv-pairs = { version = "0.1", default-features = false }
```

## License

The MIT License (MIT).
