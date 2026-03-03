# Fuzzing

This directory contains fuzz targets for the `getopt-rs` library using `cargo-fuzz` and libFuzzer.

## Prerequisites

Fuzzing requires the Rust nightly toolchain:

```bash
rustup install nightly
```

You also need `cargo-fuzz` installed:

```bash
cargo install cargo-fuzz
```

## Available Fuzz Targets

### `fuzz_getopt`
The main fuzzing target that tests arbitrary combinations of:
- Option strings (optstring)
- Command-line arguments
- opterr flag (error printing)

This target exercises all public API surfaces with randomly generated inputs.

### `fuzz_optstring`
Focuses on fuzzing the option string parser with a set of common argument patterns.
This target is useful for finding edge cases in optstring parsing logic, especially
around long options with parentheses syntax, colons for argument requirements, etc.

### `fuzz_cstr`
Tests the `&CStr` argument path, which is important for no_std and FFI use cases.
This target creates C-style null-terminated strings and feeds them to the parser
to ensure robust handling of C string inputs.

## Running Fuzzers

### Quick Test (5 seconds)
Run a fuzzer for a short time to verify it works:

```bash
cargo +nightly fuzz run fuzz_getopt -- -max_total_time=5
```

### Continuous Fuzzing
Run indefinitely until a crash is found or you stop it (Ctrl+C):

```bash
cargo +nightly fuzz run fuzz_getopt
```

### Run with More Iterations
Run with a specific number of iterations:

```bash
cargo +nightly fuzz run fuzz_getopt -- -runs=1000000
```

### Run All Fuzzers
Run each fuzzer for 1 minute:

```bash
for target in fuzz_getopt fuzz_optstring fuzz_cstr; do
    echo "Running $target..."
    cargo +nightly fuzz run $target -- -max_total_time=60
done
```

## Building Fuzz Targets

To build all fuzz targets without running them:

```bash
cargo +nightly fuzz build
```

## Listing Fuzz Targets

```bash
cargo +nightly fuzz list
```

## Corpus and Artifacts

- **Corpus**: Interesting inputs discovered during fuzzing are saved in `fuzz/corpus/<target_name>/`
- **Artifacts**: Inputs that cause crashes are saved in `fuzz/artifacts/<target_name>/`

## Minimizing a Crash

If a crash is found, you can minimize the input:

```bash
cargo +nightly fuzz cmin fuzz_getopt
```

## CI Integration

For continuous integration, you can run fuzzers for a fixed time:

```bash
# Run for 5 minutes per target
cargo +nightly fuzz run fuzz_getopt -- -max_total_time=300
cargo +nightly fuzz run fuzz_optstring -- -max_total_time=300
cargo +nightly fuzz run fuzz_cstr -- -max_total_time=300
```

## Coverage

To generate coverage reports from fuzzing:

```bash
cargo +nightly fuzz coverage fuzz_getopt
```

## More Information

- [cargo-fuzz documentation](https://rust-fuzz.github.io/book/cargo-fuzz.html)
- [libFuzzer documentation](https://llvm.org/docs/LibFuzzer.html)
