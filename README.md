# getopt-rs

A POSIX-compliant command-line option parser for Rust with GNU extensions support.

This library provides a `getopt` implementation that closely follows POSIX conventions while also supporting GNU-style long options. It's designed to be flexible, ergonomic, and suitable for both `std` and `no_std` environments.

## Features

- ✅ **POSIX-compliant** option parsing
- ✅ **GNU long options** with `--option` syntax
- ✅ **Short option aggregation** (`-abc` equivalent to `-a -b -c`)
- ✅ **Flexible argument handling** (optional, required, attached, or separate)
- ✅ **Iterator-based API** for ergonomic usage
- ✅ **`no_std` support** with optional `std` feature
- ✅ **Zero dependencies** (in `no_std` mode)
- ✅ **Type-safe option parsing** with compile-time checks
- ✅ **Works with multiple string types** (`&str`, `String`, `OsString`)

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
getopt-rs = "0.1"
```

For `no_std` environments, disable default features:

```toml
[dependencies]
getopt-rs = { version = "0.1", default-features = false }
```

## Quick Start

```rust
use getopt::Getopt;

fn main() {
    let args = &["myapp", "-a", "-b", "value", "file1", "file2"];
    let mut opts = Getopt::new(args, "ab:");
    opts.set_opterr(false); // Suppress error messages

    while let Some(opt) = opts.next() {
        match opt.val() {
            'a' => println!("Option -a provided"),
            'b' => println!("Option -b with arg: {}", opt.arg().unwrap()),
            '?' => eprintln!("Unknown option: {}", opt.erropt().unwrap()),
            _ => {}
        }
    }

    // Get remaining non-option arguments
    for arg in opts.remaining() {
        println!("Positional argument: {}", arg);
    }
}
```

## Usage Examples

### Basic Option Parsing

```rust
use getopt::Getopt;

let args = &["prog", "-a", "-b", "-c"];
let mut getopt = Getopt::new(args, "abc");

while let Some(opt) = getopt.next() {
    match opt.val() {
        'a' => println!("Got -a"),
        'b' => println!("Got -b"),
        'c' => println!("Got -c"),
        _ => {}
    }
}
```

### Options with Required Arguments

```rust
use getopt::Getopt;

let args = &["prog", "-o", "output.txt", "-v"];
let mut getopt = Getopt::new(args, "o:v");

let mut output = None;
let mut verbose = false;

while let Some(opt) = getopt.next() {
    match opt.val() {
        'o' => output = opt.into_arg(),
        'v' => verbose = true,
        _ => {}
    }
}

println!("Output: {:?}, Verbose: {}", output, verbose);
```

### Aggregated Short Options

```rust
use getopt::Getopt;

// -abc is equivalent to -a -b -c
let args = &["prog", "-abc"];
let mut getopt = Getopt::new(args, "abc");

assert_eq!(getopt.next().map(|o| o.val()), Some('a'));
assert_eq!(getopt.next().map(|o| o.val()), Some('b'));
assert_eq!(getopt.next().map(|o| o.val()), Some('c'));
```

### Long Options

```rust
use getopt::Getopt;

let args = &["prog", "--help", "--output=file.txt", "--verbose"];
let mut getopt = Getopt::new(
    args,
    "h(help)o:(output)v(verbose)"
);

while let Some(opt) = getopt.next() {
    match opt.val() {
        'h' => println!("Help requested"),
        'o' => println!("Output: {}", opt.arg().unwrap()),
        'v' => println!("Verbose mode"),
        _ => {}
    }
}
```

### Working with `std::env::args() or std::env::args_os()`

```rust
use getopt::Getopt;

fn main() {
    let mut getopt = Getopt::new(std::env::args_os(), "abc:d");
    
    while let Some(opt) = getopt.next() {
        match opt.val() {
            'a' => { /* handle -a */ },
            'b' => { /* handle -b */ },
            'c' => {
                if let Some(arg) = opt.arg() {
                    println!("Got -c with arg: {}", arg);
                }
            },
            'd' => { /* handle -d */ },
            '?' => {
                eprintln!("Unknown option: -{}", opt.erropt().unwrap());
                std::process::exit(1);
            },
            ':' => {
                eprintln!("Missing argument for option -{}", opt.erropt().unwrap());
                std::process::exit(1);
            },
            _ => {}
        }
    }
    
    // Process remaining positional arguments
    for arg in getopt.remaining() {
        println!("File: {}", arg);
    }
}
```

### Error Handling

```rust
use getopt::Getopt;

// Leading ':' in optstring changes error behavior
let args = &["prog", "-x", "-a"];
let mut getopt = Getopt::new(args, ":a:");
getopt.set_opterr(false); // Suppress error messages

while let Some(opt) = getopt.next() {
    match opt.val() {
        'a' => println!("Got -a with arg: {}", opt.arg().unwrap()),
        '?' => {
            // Unknown option
            eprintln!("Unknown option: -{}", opt.erropt().unwrap());
        },
        ':' => {
            // Missing required argument
            eprintln!("Missing argument for option -{}", opt.erropt().unwrap());
        },
        _ => {}
    }
}
```

## Option String Syntax

The option string (`optstring`) parameter follows POSIX conventions with GNU extensions:

### Basic Syntax

- **Single character**: Defines a flag option
  ```rust
  "a"       // Accepts -a
  "abc"     // Accepts -a, -b, -c
  ```

- **Character followed by `:`**: Requires an argument
  ```rust
  "a:"      // -a requires an argument: -a value or -avalue
  "a:b"     // -a takes arg, -b is a flag
  ```

- **Character followed by `::`**: Optional argument (GNU extension)
  ```rust
  "a::"     // -a with optional arg: -avalue (attached only)
  ```

### Long Options

Use parentheses to define long option names:

```rust
"h(help)"           // -h or --help
"v(verbose)"        // -v or --verbose
"o:(output)"        // -o value or --output=value
"c:(config)::"      // -c with optional arg, --config with optional arg
```

### Special Prefixes

- **Leading `:`**: Suppress error messages, return ':' for missing arguments
  ```rust
  ":abc:"   // Silent errors, returns ':' instead of '?'
  ```

- **Leading `+`**: Stop parsing at first non-option (POSIX mode)
  ```rust
  "+abc"    // Stop at first non-option argument
  ```

### Examples

```rust
// Complex option string
let optstring = "hv(verbose)o:(output)c:(config)::d(debug)";

// This accepts:
// -h, --help          (no argument)
// -v, --verbose       (no argument)
// -o value, --output=value  (required argument)
// -c, --config        (optional argument, attached only)
// -d, --debug         (no argument)
```

## Special Return Values

The `Opt::val()` method returns:

- **Option character**: When a valid option is parsed
- **`'?'`**: When an unknown option is encountered (or any error if optstring doesn't start with `:`)
- **`':'`**: When a required argument is missing (only if optstring starts with `:`)

Use `Opt::erropt()` to get the problematic option character when an error occurs.

## Program Name Handling

The first argument (argv\[0\]) is consumed and used as the program name:

```rust
use getopt::Getopt;

let args = &["/usr/bin/myapp", "-a"];
let getopt = Getopt::new(args, "a");

assert_eq!(getopt.prog_name(), "myapp");  // Basename extracted
```

## `no_std` Support

The library supports `no_std` environments. Disable the default `std` feature:

```toml
[dependencies]
getopt = { version = "0.1", default-features = false }
```

In `no_std` mode:
- Error messages are not printed (no stderr)
- `OsString` support is unavailable
- Core functionality remains the same

## API Overview

### `Opt` Structure

Represents a parsed option:

```rust
pub struct Opt {
    pub val: char,              // Option character or error indicator
    pub erropt: Option<char>,   // Problematic option if error occurred
    pub arg: Option<String>,    // Option argument if provided
}
```

Methods:
- `val(&self) -> char` - Get the option character
- `erropt(&self) -> Option<char>` - Get the error option character
- `arg(&self) -> Option<&str>` - Get option argument (borrowed)
- `into_arg(self) -> Option<String>` - Get option argument (owned)

### `Getopt` Structure

Iterator-based option parser:

```rust
pub struct Getopt<'a, V, I: Iterator<Item = V>> { /* ... */ }
```

Methods:
- `new(args, optstring, opterr) -> Self` - Create new parser
- `next(&mut self) -> Option<Opt>` - Parse next option (implements `Iterator`)
- `remaining(self) -> I` - Get remaining unparsed arguments
- `prog_name(&self) -> &str` - Get the program name

### `ArgV` Trait

Implemented for types that can be converted to strings for argument parsing:
- `&str`
- `String`
- `OsString` (with `std` feature)

## Testing

The library includes comprehensive tests covering:
- POSIX compliance scenarios
- GNU extensions
- Error handling
- Edge cases

Run tests with:
```bash
cargo test
```

For `no_std` testing:
```bash
cargo test --no-default-features
```

### Fuzzing

This library includes fuzzing targets to ensure robustness and catch potential panics. The fuzzers use `cargo-fuzz` and libFuzzer.

Install fuzzing tools:
```bash
cargo install cargo-fuzz
rustup install nightly
```

Run all fuzzers for 60 seconds each:
```bash
./fuzz/run-all-fuzzers.sh 60
```

Or run a specific fuzzer:
```bash
cargo +nightly fuzz run fuzz_getopt -- -max_total_time=60
```

See the [fuzz/README.md](fuzz/README.md) for detailed fuzzing documentation.

## License

BSD 2-Clause License

## Contributing

Contributions are welcome! Please ensure all tests pass and add new tests for any new features.
