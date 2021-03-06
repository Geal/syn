#![cfg(feature = "full")]

#![feature(rustc_private)]

#[macro_use]
extern crate quote;
extern crate rayon;
extern crate syn;
extern crate syntax;
extern crate walkdir;

use rayon::iter::{ParallelIterator, IntoParallelIterator};
use syntax::ast;
use syntax::parse::{self, ParseSess, PResult};
use syntax::codemap::FilePathMapping;
use walkdir::{WalkDir, WalkDirIterator, DirEntry};

use std::fs::File;
use std::io::Read;
use std::panic;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

#[allow(dead_code)]
#[macro_use]
mod common;

#[test]
fn test_round_trip() {
    common::check_min_stack();
    common::clone_rust();
    let abort_after = common::abort_after();
    if abort_after == 0 {
        panic!("Skipping all round_trip tests");
    }

    let failed = AtomicUsize::new(0);

    WalkDir::new("tests/rust")
        .sort_by(|a, b| a.cmp(b))
        .into_iter()
        .filter_entry(common::base_dir_filter)
        .collect::<Result<Vec<DirEntry>, walkdir::Error>>()
        .unwrap()
        .into_par_iter()
        .for_each(|entry|
    {
        let path = entry.path();
        if path.is_dir() {
            return;
        }

        let mut file = File::open(path).unwrap();
        let mut content = String::new();
        file.read_to_string(&mut content).unwrap();

        let start = Instant::now();
        let (krate, elapsed) = match syn::parse_file(&content) {
            Ok(krate) => (krate, start.elapsed()),
            Err(msg) => {
                errorf!("=== {}: syn failed to parse\n{:?}\n",
                        path.display(),
                        msg);
                let prev_failed = failed.fetch_add(1, Ordering::SeqCst);
                if prev_failed + 1 >= abort_after {
                    panic!("Aborting Immediately due to ABORT_AFTER_FAILURE");
                }
                return;
            }
        };
        let back = quote!(#krate).to_string();

        let equal = panic::catch_unwind(|| {
            let sess = ParseSess::new(FilePathMapping::empty());
            let before = match libsyntax_parse(content, &sess) {
                Ok(before) => before,
                Err(mut diagnostic) => {
                    diagnostic.cancel();
                    if diagnostic.message().starts_with("file not found for module") {
                        errorf!("=== {}: ignore\n", path.display());
                    } else {
                        errorf!("=== {}: ignore - libsyntax failed to parse original content: {}\n",
                                path.display(),
                                diagnostic.message());
                    }
                    return true;
                }
            };
            let after = match libsyntax_parse(back, &sess) {
                Ok(after) => after,
                Err(mut diagnostic) => {
                    errorf!("=== {}: libsyntax failed to parse", path.display());
                    diagnostic.emit();
                    return false;
                }
            };

            if before == after {
                errorf!("=== {}: pass in {}ms\n",
                        path.display(),
                        elapsed.as_secs() * 1000 + elapsed.subsec_nanos() as u64 / 1_000_000);
                true
            } else {
                errorf!("=== {}: FAIL\nbefore: {}\nafter: {}\n",
                        path.display(),
                        format!("{:?}", before).replace("\n", ""),
                        format!("{:?}", after).replace("\n", ""));
                false
            }
        });
        match equal {
            Err(_) => errorf!("=== {}: ignoring libsyntax panic\n", path.display()),
            Ok(true) => {}
            Ok(false) => {
                let prev_failed = failed.fetch_add(1, Ordering::SeqCst);
                if prev_failed + 1 >= abort_after {
                    panic!("Aborting Immediately due to ABORT_AFTER_FAILURE");
                }
            },
        }
    });

    let failed = failed.load(Ordering::SeqCst);
    if failed > 0 {
        panic!("{} failures", failed);
    }
}

fn libsyntax_parse(content: String, sess: &ParseSess) -> PResult<ast::Crate> {
    let name = "test_round_trip".to_string();
    parse::parse_crate_from_source_str(name, content, sess)
        .map(common::respan::respan_crate)
}
