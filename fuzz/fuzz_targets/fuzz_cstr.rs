#![no_main]

use libfuzzer_sys::fuzz_target;
use arbitrary::{Arbitrary, Unstructured};
use core::ffi::CStr;

#[derive(Debug, Arbitrary)]
struct CStrInput<'a> {
    optstring: &'a str,
    // Raw bytes that we'll try to interpret as null-terminated C strings
    arg_bytes: Vec<u8>,
}

fuzz_target!(|data: &[u8]| {
    let mut unstructured = Unstructured::new(data);
    if let Ok(input) = CStrInput::arbitrary(&mut unstructured) {
        // Try to create CStr arguments from the fuzzed bytes
        // Split on null bytes to create multiple CStr arguments
        let mut args: Vec<&CStr> = Vec::new();
        let mut start = 0;
        
        for (i, &byte) in input.arg_bytes.iter().enumerate() {
            if byte == 0 && i > start {
                // Found a null byte, try to create a CStr
                if let Ok(cstr) = CStr::from_bytes_with_nul(&input.arg_bytes[start..=i]) {
                    args.push(cstr);
                    start = i + 1;
                }
            }
        }
        
        // Need at least a program name
        if args.is_empty() {
            return;
        }
        
        // Create getopt with CStr arguments
        let mut getopt = getopt_rs::Getopt::new(
            args.into_iter(),
            input.optstring,
            false,
        );
        
        // Consume all options - should never panic
        while let Some(opt) = getopt.next() {
            let _ = opt.val();
            let _ = opt.erropt();
            let _ = opt.arg();
        }
        
        let _ = getopt.prog_name();
        
        // Consume remaining - CStr iteration should never panic
        for _ in getopt.remaining() {}
    }
});
