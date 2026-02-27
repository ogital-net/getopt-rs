use std::ffi::{CStr, CString, OsString, c_char, c_int};

#[link(name = "c")]
unsafe extern "C" {
    static optarg: *const c_char;
    static mut optind: c_int;
    static optopt: c_int;
    static mut opterr: c_int;
    #[cfg(not(target_os = "linux"))]
    static mut optreset: c_int;
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

mod sealed {
    pub trait Sealed {}

    impl Sealed for &str {}
    impl Sealed for String {}
    impl Sealed for std::ffi::OsString {}
}

pub trait ArgV: sealed::Sealed {
    fn to_cstring(self) -> CString;
}

impl ArgV for &str {
    fn to_cstring(self) -> CString {
        let vec: Vec<u8> = self.as_bytes().into();
        unsafe { CString::from_vec_unchecked(vec) }
    }
}

impl ArgV for String {
    fn to_cstring(self) -> CString {
        unsafe { CString::from_vec_unchecked(self.into_bytes()) }
    }
}

impl ArgV for OsString {
    fn to_cstring(self) -> CString {
        unsafe { CString::from_vec_unchecked(self.into_encoded_bytes()) }
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
pub struct Getopt {
    args: Vec<CString>,
    pointers: Vec<*mut c_char>,
    optstring: CString,
}

impl Getopt {
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
    /// let opts = Getopt::new(args, "f:", true);
    /// ```
    pub fn new<A, V, O>(args: A, optstring: O, log_err: bool) -> Self
    where
        A: IntoIterator<Item = V>,
        V: ArgV,
        O: Into<Vec<u8>>,
    {
        reset_globals(log_err);
        let i = args.into_iter();
        let mut args: Vec<CString> = Vec::new();
        let mut pointers: Vec<*mut c_char> = Vec::new();

        if let Some(size) = i.size_hint().1 {
            args.reserve_exact(size);
            pointers.reserve_exact(size);
        };
        for v in i {
            let cs = v.to_cstring();
            let ptr = cs.as_ptr() as *const _ as *mut c_char;
            args.push(cs);
            pointers.push(ptr);
        }
        let optstring = unsafe { CString::from_vec_unchecked(optstring.into()) };

        Self {
            args,
            pointers,
            optstring,
        }
    }

    /// Create a `Getopt` instance using the current process's
    /// [`std::env::args_os()`] iterator as the argument source.
    ///
    /// This is a thin wrapper around [`Getopt::new`], passing through the
    /// command-line arguments supplied by the operating system. It is useful
    /// for applications that want to parse their own arguments without first
    /// collecting them into a `Vec`.
    ///
    /// # Arguments
    ///
    /// * `optstring` - option specification string, same as for [`Getopt::new`]
    /// * `log_err` - controls whether missing/invalid options are printed to
    ///   stderr.
    ///
    /// [`std::env::args_os()`]: https://doc.rust-lang.org/std/env/fn.args_os.html
    pub fn from_args_os<O>(optstring: O, log_err: bool) -> Self
    where
        O: Into<Vec<u8>>,
    {
        Self::new(std::env::args_os(), optstring, log_err)
    }

    /// Same as [`from_args_os`], but uses [`std::env::args()`] which returns
    /// `String` values. This is convenient when the arguments are known to be
    /// valid UTF‑8.
    ///
    /// The parameters have the same meaning as for [`Getopt::new`].
    ///
    /// [`std::env::args()`]: https://doc.rust-lang.org/std/env/fn.args.html
    pub fn from_args<O>(optstring: O, log_err: bool) -> Self
    where
        O: Into<Vec<u8>>,
    {
        Self::new(std::env::args(), optstring, log_err)
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
    /// let opts = Getopt::new(args, "f:", true);
    /// let _parsed: Vec<_> = opts.into_iter().collect();
    /// assert_eq!(opts.remaining(), &["arg1", "arg2"]);
    /// ```
    pub fn remaining(&self) -> Vec<&str> {
        unsafe { &self.args[(optind as usize)..] }
            .iter()
            .map(|v| core::str::from_utf8(v.as_bytes()).unwrap())
            .collect()
    }
}

impl<'a> Iterator for &'a Getopt {
    type Item = Opt<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let res = unsafe {
            libc::getopt(
                self.pointers.len() as c_int,
                self.pointers.as_ptr(),
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
                // UTF-8 may not be guaranteed; return `None` on failure rather than
                // panic.  This mirrors the behaviour of `String::from_utf8_lossy`
                // but avoids allocation.
                cstr.to_str().ok()
            }
        };

        Some(Opt {
            val: opt,
            erropt,
            arg,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        #[cfg(not(target_os = "linux"))]
        let start_index = unsafe { optind as usize };

        #[cfg(target_os = "linux")]
        // GNU getopt uses 0 for reset
        let start_index = unsafe { if optind > 0 { optind as usize } else { 1 } };

        let len = self.args.len();
        if start_index < len {
            (0, Some(len - start_index))
        } else {
            (0, Some(0))
        }
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
        let getopt = Getopt::new(args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), 'f');
        assert_eq!(parsed[0].arg(), Some("path"));
        assert_eq!(parsed[0].erropt(), None);
    }

    #[test]
    fn test_size_hint() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-a", "-b"];
        let getopt = Getopt::new(args, "ab", false);
        let mut iter = &getopt;

        // initial upper bound includes both options (`len - 1`)
        assert_eq!(iter.size_hint(), (0, Some(2)));

        // consume one option and check hint again
        iter.next();
        assert_eq!(iter.size_hint(), (0, Some(1)));

        // consume second option -> no remaining items
        iter.next();
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_missing_arg() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-f"];
        let getopt = Getopt::new(args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), '?');
        assert_eq!(parsed[0].erropt(), Some('f'));
    }

    #[test]
    fn test_missing_arg_colon() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-f"];
        let getopt = Getopt::new(args, ":f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), ':');
        assert_eq!(parsed[0].erropt(), Some('f'));
    }

    #[test]
    fn test_unknown_option() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-x"];
        let getopt = Getopt::new(args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), '?');
        assert_eq!(parsed[0].erropt(), Some('x'));
    }

    #[test]
    fn test_multiple_options() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-a", "-b", "value", "-c"];
        let getopt = Getopt::new(args, "ab:c", false);
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
        let getopt = Getopt::new(args, "a", false);
        let _parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(getopt.remaining(), &["file1", "file2"]);
    }

    #[test]
    fn test_opt_equality() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-f", "path"];
        let getopt = Getopt::new(args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();

        // Test direct equality with char
        assert!(parsed[0] == 'f');
        assert!(parsed[0] != 'x');

        // Test with references
        assert_eq!(&parsed[0], &'f');
        assert_ne!(&parsed[0], &'x');
    }
}
