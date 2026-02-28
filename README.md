# getopt-rs

A Rust wrapper for the Unix getopt function for parsing command line arguments.

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
getopt-rs = "0.1.0"
```

## Usage

This library provides a safe Rust interface to the Unix `getopt` function for parsing command-line options. It supports both simple flags and options with values.

### Basic Usage

```rust
use getopt_rs::Getopt;

fn main() {
    // assuming
    // program -a -b value -c file1 file2
    let getopt = Getopt::new(std::env::args_os(), "ab:c", true);

    // Iterate over the options
    for opt in &getopt {
        match opt.val() {
            'a' => println!("Flag -a was set"),
            'b' => println!("Option -b had value: {}", opt.arg().unwrap()),
            'c' => println!("Flag -c was set"),
            '?' => println!("Unknown option: -{}", opt.erropt().unwrap()),
            _ => unreachable!()
        }
    }

    // Process remaining arguments
    println!("Remaining arguments: {:?}", getopt.remaining());
}
```

### Convenience Constructors

If you simply want to parse your own process's arguments without
collecting them into a container, the library provides two wrappers:

```rust
use getopt_rs::Getopt;

fn main() {
    // the same option string as above
    let getopt = Getopt::from_args("ab:c", true);
    for opt in &getopt {
        // handle options as before
    }

    // or use `args_os` when non-UTF8 values may appear:
    let getopt_os = Getopt::from_args_os("ab:c", true);
    for opt in &getopt_os {
        // identical behaviour
    }
}
```

### Option String Format

The option string follows Unix getopt conventions:
- Must be single byte characters
- Single letters represent flags (e.g. `"ab"` allows `-a` and `-b` flags)
- Letters followed by `:` represent options that take values (e.g. `"a:b:"` means `-a value -b value`)
- Is passed directly to the system's libc getopt() function permitting any platform specifc extensions


### Error Handling

The library handles two types of errors:
- Unknown options: Returns an `Opt` with `val() == '?'` and `erropt()` containing the invalid option
- Missing arguments:
  - If optstring starts with ':': Returns an `Opt` with `val() == ':'` and `erropt()` containing the option
  - Otherwise: Returns an `Opt` with `val() == '?'` and `erropt()` containing the option

### Option Comparison

Options can be directly compared with characters:

```rust
use getopt_rs::Getopt;

let args: Vec<String> = std::env::args().collect();
let getopt = Getopt::new(&args, "a", true);
if let Some(opt) = getopt.into_iter().next() {
    assert!(opt == 'a');
}
```

## Examples

### Parse input/output file options

```rust
use getopt_rs::Getopt;

let args = vec!["program", "-i", "input.txt", "-o", "output.txt", "-v"];
let getopt = Getopt::new(args, "i:o:v", true);

let mut input_file = None;
let mut output_file = None;
let mut verbose = false;

for opt in &getopt {
    match opt.val() {
        'i' => input_file = opt.arg(),
        'o' => output_file = opt.arg(),
        'v' => verbose = true,
        '?' => eprintln!("Unknown option: -{}", opt.erropt().unwrap()),
        _ => {}
    }
}

assert_eq!(input_file, Some("input.txt"));
assert_eq!(output_file, Some("output.txt"));
assert!(verbose);
```

### Access program name for usage messages

```rust
use getopt_rs::Getopt;

let args = vec!["/usr/bin/myapp", "-h"];
let getopt = Getopt::new(args, "h", true);

let program = getopt.prog_name();  // "myapp"
let full_path = getopt.file_name(); // "/usr/bin/myapp"

for opt in &getopt {
    if opt.val() == 'h' {
        println!("Usage: {} [OPTIONS] FILES...", program);
    }
}
```

### Handle multiple flags and positional arguments

```rust
use getopt_rs::Getopt;

let args = vec!["cmd", "-abc", "file1.txt", "file2.txt"];
let getopt = Getopt::new(args, "abc", true);

let mut flags = Vec::new();
for opt in &getopt {
    match opt.val() {
        'a' | 'b' | 'c' => flags.push(opt.val()),
        _ => {}
    }
}

let remaining = getopt.remaining();
assert_eq!(flags, vec!['a', 'b', 'c']);
assert_eq!(remaining, vec!["file1.txt", "file2.txt"]);
```

### Handle invalid UTF-8 arguments

When command-line arguments may contain non-UTF-8 sequences, use `OsString` and `from_args_os`.  Invalid UTF-8 are replaced.

## License

BSD-2-Clause

Copyright 2026 Latigo LLC

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.