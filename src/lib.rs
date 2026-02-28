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
    // SAFETY: an interior null byte is simply viewed as a shorter string by getopt
    fn to_cstring(self) -> CString {
        let vec: Vec<u8> = self.as_bytes().into();
        unsafe { CString::from_vec_unchecked(vec) }
    }
}

impl ArgV for String {
    // SAFETY: an interior null byte is simply viewed as a shorter string by getopt
    fn to_cstring(self) -> CString {
        unsafe { CString::from_vec_unchecked(self.into_bytes()) }
    }
}

impl ArgV for OsString {
    fn to_cstring(self) -> CString {
        let s = match self.into_string() {
            Ok(s) => s,
            Err(o) => o.to_string_lossy().into_owned(),
        };
        // SAFETY: an interior null byte is simply viewed as a shorter string by getopt
        unsafe { CString::from_vec_unchecked(s.into_bytes()) }
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
        if self.args.is_empty() {
            return Vec::new();
        }

        self.args[self.next_index()..]
            .iter()
            .map(|v| unsafe { std::str::from_utf8_unchecked(v.as_bytes()) })
            .collect()
    }

    /// Returns the full file name or path of the program being run.
    ///
    /// This is the first argument supplied to the parser (typically `argv[0]`),
    /// which is usually the program name or path as invoked by the shell.
    ///
    /// # Returns
    ///
    /// - The first argument as a string slice if arguments were provided
    /// - An empty string if no arguments were provided
    ///
    /// # Example
    ///
    /// ```
    /// use getopt_rs::Getopt;
    /// let args = vec!["/usr/bin/myapp", "-f", "file.txt"];
    /// let getopt = Getopt::new(args, "f:", false);
    /// assert_eq!(getopt.file_name(), "/usr/bin/myapp");
    /// ```
    pub fn file_name(&self) -> &str {
        match self.args.is_empty() {
            true => "",
            false => unsafe { std::str::from_utf8_unchecked(self.args[0].as_bytes()) },
        }
    }

    /// Returns the program name (basename) without the directory path.
    ///
    /// This extracts the base name of the program by finding the last '/' character
    /// in the file path and returning everything after it. If no '/' is found,
    /// the entire file name is returned.
    ///
    /// # Returns
    ///
    /// - The program name (basename) without directory components
    /// - An empty string if no arguments were provided
    ///
    /// # Example
    ///
    /// ```
    /// use getopt_rs::Getopt;
    /// let args = vec!["/usr/bin/myapp", "-f", "file.txt"];
    /// let getopt = Getopt::new(args, "f:", false);
    /// assert_eq!(getopt.prog_name(), "myapp");
    /// ```
    pub fn prog_name(&self) -> &str {
        const PATH_SEP: char = '/';

        let s = self.file_name();
        if let Some(idx) = s.rfind(PATH_SEP) {
            return &s[(idx + 1)..];
        }
        s
    }

    #[cfg(not(target_os = "linux"))]
    fn next_index(&self) -> usize {
        unsafe { optind as usize }.min(self.args.len())
    }

    #[cfg(target_os = "linux")]
    fn next_index(&self) -> usize {
        // GNU and musl getopt uses 0 for reset
        unsafe { if optind > 0 { optind as usize } else { 1 } }.min(self.args.len())
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
                // SAFETY: the strings provided were all verified to be UTF-8
                Some(std::str::from_utf8_unchecked(
                    CStr::from_ptr(optarg).to_bytes(),
                ))
            }
        };

        Some(Opt {
            val: opt,
            erropt,
            arg,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.args.is_empty() {
            return (0, Some(0));
        }
        (0, Some(self.args.len() - self.next_index()))
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
    fn test_empty_args() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let getopt = Getopt::new(Vec::<String>::new(), "a", false);

        let _parsed: Vec<Opt> = getopt.into_iter().collect();
        assert!(getopt.remaining().is_empty());
    }

    #[test]
    fn test_remaining_args() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-a", "file1", "file2"];
        let getopt = Getopt::new(args, "a", false);
        assert_eq!(getopt.remaining(), &["-a", "file1", "file2"]);
        let _parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(getopt.remaining(), &["file1", "file2"]);
    }

    #[test]
    fn test_verifies_optind_bounds() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["cmd", "-a", "-b", "-c"];
        let getopt = Getopt::new(args, ":a:b:c:d:", false);
        let mut getopt = getopt.into_iter();
        for _i in 1..10 {
            getopt.next();
        }
        assert_eq!(getopt.size_hint().1, Some(0));
        assert!(getopt.remaining().is_empty());
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

    #[test]
    fn test_non_utf8_option_arg() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        // Construct an argument list where the option's argument contains
        // invalid UTF-8.
        let mut args: Vec<OsString> = Vec::with_capacity(4);
        args.push(OsString::from("cmd"));
        args.push(OsString::from("-f"));
        let mut bad_bytes = vec![0xff, 0xfe]; // not valid UTF-8
        bad_bytes.extend_from_slice(b"ABCD");
        args.push(unsafe { OsString::from_encoded_bytes_unchecked(bad_bytes) });
        let mut bad_bytes = vec![0xff, 0xfe];
        bad_bytes.extend_from_slice(b"EFGH");
        args.push(unsafe { OsString::from_encoded_bytes_unchecked(bad_bytes) });

        let getopt = Getopt::new(args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), 'f');
        assert_eq!(parsed[0].arg(), Some("��ABCD"));
        assert_eq!(getopt.remaining(), vec!["��EFGH"]);
    }

    #[test]
    fn test_handles_interior_nulls_gracefully() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        // Construct an argument list where the option's argument contains
        // invalid UTF-8.
        let mut args: Vec<String> = Vec::with_capacity(4);
        args.push("cmd".into());
        args.push("-f".into());
        let mut bad_string: String = "ABCD".into();
        bad_string.push(0 as char);
        bad_string.push_str("EFGH");
        args.push(bad_string);

        let getopt = Getopt::new(args, "f:", false);
        let parsed: Vec<Opt> = getopt.into_iter().collect();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].val(), 'f');
        assert_eq!(parsed[0].arg(), Some("ABCD"));
    }

    #[test]
    fn test_file_name_with_path() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["/usr/bin/myapp", "-f", "file.txt"];
        let getopt = Getopt::new(args, "f:", false);
        assert_eq!(getopt.file_name(), "/usr/bin/myapp");
    }

    #[test]
    fn test_file_name_without_path() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["myapp", "-f", "file.txt"];
        let getopt = Getopt::new(args, "f:", false);
        assert_eq!(getopt.file_name(), "myapp");
    }

    #[test]
    fn test_file_name_empty_args() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let getopt = Getopt::new(Vec::<String>::new(), "f:", false);
        assert_eq!(getopt.file_name(), "");
    }

    #[test]
    fn test_prog_name_with_full_path() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["/usr/bin/myapp", "-f", "file.txt"];
        let getopt = Getopt::new(args, "f:", false);
        assert_eq!(getopt.prog_name(), "myapp");
    }

    #[test]
    fn test_prog_name_without_path() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["myapp", "-f", "file.txt"];
        let getopt = Getopt::new(args, "f:", false);
        assert_eq!(getopt.prog_name(), "myapp");
    }

    #[test]
    fn test_prog_name_deep_nested_path() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let args = vec!["/very/long/nested/path/to/myapp", "-f", "file.txt"];
        let getopt = Getopt::new(args, "f:", false);
        assert_eq!(getopt.prog_name(), "myapp");
    }

    #[test]
    fn test_prog_name_trailing_slash() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        // Edge case: if argv[0] ends with a slash, prog_name returns empty string
        let args = vec!["/usr/bin/", "-f"];
        let getopt = Getopt::new(args, "f:", false);
        assert_eq!(getopt.prog_name(), "");
    }

    #[test]
    fn test_prog_name_empty_args() {
        let _lock = GLOBAL_LOCK.lock().unwrap();

        let getopt = Getopt::new(Vec::<String>::new(), "f:", false);
        assert_eq!(getopt.prog_name(), "");
    }
}
