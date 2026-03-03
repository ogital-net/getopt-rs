#![no_main]

use libfuzzer_sys::fuzz_target;
use arbitrary::{Arbitrary, Unstructured};

#[derive(Debug, Arbitrary)]
struct FuzzInput<'a> {
    optstring: &'a str,
    args: Vec<&'a str>,
    opterr: bool,
}

fuzz_target!(|data: &[u8]| {
    // Parse arbitrary data into our input structure
    let mut unstructured = Unstructured::new(data);
    if let Ok(input) = FuzzInput::arbitrary(&mut unstructured) {
        // Skip empty args as that's not a useful test case
        if input.args.is_empty() {
            return;
        }

        // Create getopt parser with fuzzed inputs
        let mut getopt = getopt_rs::Getopt::new(
            input.args.iter().copied(),
            input.optstring,
            input.opterr,
        );

        // Consume all options - this should never panic
        while let Some(opt) = getopt.next() {
            // Access all fields to ensure they're valid
            let _ = opt.val();
            let _ = opt.erropt();
            let _ = opt.arg();
        }

        // Access prog_name - should never panic
        let _ = getopt.prog_name();

        // Consume remaining args - should never panic
        for _arg in getopt.remaining() {
            // Just iterate, don't need to do anything
        }
    }
});
