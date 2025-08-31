use std::ffi::{c_char, c_int, CStr, CString};

#[link(name = "c")]
unsafe extern "C" {
    static optarg: *const c_char;
    static mut optind: c_int;
    static optopt: c_int;
    static mut opterr: c_int;
    #[cfg(not(target_os = "linux"))]
    static mut optreset: c_int;

    #[cfg_attr(
        all(target_os = "macos", target_arch = "x86"),
        link_name = "getopt$UNIX2003"
    )]
    fn getopt(argc: c_int, argv: *const *mut c_char, optstr: *const c_char) -> c_int;    
}

// reset inspired by https://github.com/dnsdb/dnsdbq/commit/efa68c0499c3b5b4a1238318345e5e466a7fd99f
#[cfg(not(target_os = "linux"))]
fn reset_globals(log_err: bool) {
    unsafe {
        opterr = match log_err {
            true => 1,
            false => 0,
        };
        optind = 1;
        optreset = 1;
    }
}

#[cfg(target_os = "linux")]
fn reset_globals(log_err: bool) {
    unsafe {
        opterr = match log_err {
            true => 1,
            false => 0,
        };
        optind = 0;
    }
}

#[derive(Debug)]
pub struct Opt<'a> {
    val: char,
    erropt: Option<char>,
    arg: Option<&'a str>,
}

impl<'a> Opt<'a> {
    /// Returns the option character that was parsed.
    ///
    /// This can be:
    /// - The actual option character if it was valid
    /// - '?' if an unknown option was encountered
    /// - ':' if a missing argument was detected and optstring starts with ':'
    pub fn val(&self) -> char {
        self.val
    }

    /// Returns the error option character if an error occurred during parsing.
    ///
    /// Returns:
    /// - `Some(char)` containing the problematic option character if:
    ///   - An unknown option was encountered
    ///   - A required argument was missing
    /// - `None` if no error occurred
    pub fn erropt(&self) -> Option<char> {
        self.erropt
    }

    /// Returns the argument associated with the option, if any.
    ///
    /// Returns:
    /// - `Some(&str)` containing the option's argument if one was provided
    /// - `None` if the option takes no argument or if a required argument was missing
    pub fn arg(&self) -> Option<&'a str> {
        self.arg
    }
}

impl PartialEq<char> for Opt<'_> {
    fn eq(&self, other: &char) -> bool {
        self.val == *other
    }
}

/// A Rust wrapper for the Unix getopt function for parsing command line arguments.
///
/// # Thread Safety
///
/// **Warning**: This type is not thread-safe. The underlying libc `getopt` function uses
/// global state and is not reentrant. Multiple instances of `Getopt` must not be used
/// concurrently from different threads.
///
/// To safely use this type in tests or multi-threaded code:
/// - Use a mutex to synchronize access (see the test module for an example)
/// - Create and complete iteration of one `Getopt` instance before creating another
/// - Do not share `Getopt` instances between threads
pub struct Getopt<'a, A> {
    args: &'a [A],
    c_args: Vec<CString>,
    c_args_ptrs: Vec<*mut c_char>,
    optstring: CString,
}

impl<'a, A> Getopt<'a, A> {
    /// Creates a new Getopt parser with the specified arguments and option string.
    ///
    /// # Arguments
    /// * `args` - An iterator yielding the program arguments (including the program name)
    /// * `optstring` - A string containing the valid options:
    ///   - Each character represents a valid option
    ///   - A character followed by ':' indicates that option requires an argument
    ///   - If optstring starts with ':', then missing arguments are reported differently
    /// * `log_err` - Controls logging of missing/invalid options to stderr
    ///
    /// # Example
    /// ```
    /// use getopt_rs::Getopt;
    /// let args = vec!["program", "-f", "file.txt"];
    /// let opts = Getopt::new(&args, "f:", true);
    /// ```
    pub fn new<O>(args: &'a [A], optstring: O, log_err: bool) -> Self
    where
        A: Into<Vec<u8>> + Clone,
        O: Into<Vec<u8>>,
    {
        reset_globals(log_err);

        let c_args: Vec<CString> = args
            .iter()
            .map(|s| CString::new((*s).clone()).unwrap())
            .collect();
        let c_args_ptrs: Vec<*mut c_char> = c_args
            .iter()
            .map(|v| v.as_ptr() as *mut c_char)
            .collect();
        let optstring = CString::new(optstring).unwrap();
        Self {
            args,
            c_args,
            c_args_ptrs,
            optstring,
        }
    }

    /// Returns a slice containing the remaining unparsed arguments.
    ///
    /// This method should be called after iteration is complete to retrieve any
    /// non-option arguments that appeared after the options.
    ///
    /// # Example
    /// ```
    /// use getopt_rs::Getopt;
    /// let args = vec!["program", "-f", "file.txt", "arg1", "arg2"];
    /// let opts = Getopt::new(&args, "f:", true);
    /// let _parsed: Vec<_> = opts.into_iter().collect();
    /// assert_eq!(opts.remaining(), &["arg1", "arg2"]);
    /// ```
    pub fn remaining(&self) -> &[A] {
        unsafe { &self.args[(optind as usize)..] }
    }
}

impl<'a, A> Iterator for &'a Getopt<'_, A> {
    type Item = Opt<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let res = unsafe {
            getopt(
                self.c_args.len() as c_int,
                self.c_args_ptrs.as_ptr(),
                self.optstring.as_ptr(),
            )
        };
        if res == -1 {
            return None;
        }
        // The getopt() function shall return the next option character specified on the command line.
        let opt = res as u8 as char;
        let mut erropt = None;

        // A question mark ( '?' ) shall be returned if getopt() encounters an option character not
        // in optstring or detects a missing argument and the first character of optstring was not
        // a colon ( ':' ).
        if opt == '?' {
            unsafe { erropt = Some(optopt as u8 as char) }
        } else {
            // A colon ( ':' ) shall be returned if getopt() detects a missing argument and the first
            // character of optstring was a colon ( ':' )
            if self.optstring.as_bytes()[0] == b':' && opt == ':' {
                unsafe { erropt = Some(optopt as u8 as char) }
            }
        }
        let arg = unsafe {
            if optarg.is_null() {
                None
            } else {
                let cstr = CStr::from_ptr(optarg);
                Some(cstr.to_str().unwrap())
            }
        };

        Some(Opt {
            val: opt,
            erropt,
            arg,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use super::*;

    static GLOBAL_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn test_basic_getopt() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-f", "path"];
        let getopt = Getopt::new(&args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), 'f');
        assert_eq!(parsed[0].arg(), Some("path"));
        assert_eq!(parsed[0].erropt(), None);
    }

    #[test]
    fn test_missing_arg() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-f"];
        let getopt = Getopt::new(&args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), '?');
        assert_eq!(parsed[0].erropt(), Some('f'));
    }

    #[test]
    fn test_missing_arg_colon() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-f"];
        let getopt = Getopt::new(&args, ":f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), ':');
        assert_eq!(parsed[0].erropt(), Some('f'));
    }

    #[test]
    fn test_unknown_option() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-x"];
        let getopt = Getopt::new(&args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), '?');
        assert_eq!(parsed[0].erropt(), Some('x'));
    }

    #[test]
    fn test_multiple_options() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-a", "-b", "value", "-c"];
        let getopt = Getopt::new(&args, "ab:c", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 3);

        assert_eq!(parsed[0].val(), 'a');
        assert_eq!(parsed[0].arg(), None);

        assert_eq!(parsed[1].val(), 'b');
        assert_eq!(parsed[1].arg(), Some("value"));

        assert_eq!(parsed[2].val(), 'c');
        assert_eq!(parsed[2].arg(), None);
    }

    #[test]
    fn test_remaining_args() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-a", "file1", "file2"];
        let getopt = Getopt::new(&args, "a", false);
        let _parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(getopt.remaining(), &["file1", "file2"]);
    }

    #[test]
    fn test_opt_equality() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-f", "path"];
        let getopt = Getopt::new(&args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();

        // Test direct equality with char
        assert!(parsed[0] == 'f');
        assert!(parsed[0] != 'x');

        // Test with references
        assert_eq!(&parsed[0], &'f');
        assert_ne!(&parsed[0], &'x');
    }
}
