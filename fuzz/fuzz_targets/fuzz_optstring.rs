#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Try to interpret the data as a UTF-8 string for optstring
    if let Ok(optstring) = core::str::from_utf8(data) {
        // Use a set of common argument patterns
        let test_args_sets = [
            vec!["prog"],
            vec!["prog", "-a"],
            vec!["prog", "-a", "-b"],
            vec!["prog", "-abc"],
            vec!["prog", "-a", "value"],
            vec!["prog", "-avalue"],
            vec!["prog", "--help"],
            vec!["prog", "--option=value"],
            vec!["prog", "--option", "value"],
            vec!["prog", "-a", "--", "-b"],
            vec!["prog", "-a", "-b", "file1", "file2"],
            vec!["prog", "-"],
            vec!["prog", "--"],
        ];

        for args in test_args_sets.iter() {
            // Test with opterr true and false
            for opterr in [true, false] {
                let mut getopt = getopt_rs::Getopt::new(
                    args.iter().copied(),
                    optstring,
                    opterr,
                );

                // Consume all options - should never panic
                while let Some(opt) = getopt.next() {
                    let _ = opt.val();
                    let _ = opt.erropt();
                    let _ = opt.arg();
                }

                let _ = getopt.prog_name();
                
                // Consume remaining
                for _ in getopt.remaining() {}
            }
        }
    }
});
