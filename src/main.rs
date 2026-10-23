use kefir::{AxiomPolicy, InputError, Outcome, Run};
use std::panic::{AssertUnwindSafe, catch_unwind};

fn exit_code(outcome: Outcome) -> i32 {
    match outcome {
        Outcome::Accept => 0,
        Outcome::Reject => 1,
        Outcome::Decline => 2,
        Outcome::InputError | Outcome::InternalError => 3,
    }
}
fn arguments_from(
    args: impl IntoIterator<Item = std::ffi::OsString>,
) -> Result<(bool, AxiomPolicy), InputError> {
    let mut declarations = false;
    let mut policy = None;
    for arg in args {
        if cfg!(feature = "introspection") && arg == "--declarations" && !declarations {
            declarations = true;
        } else if arg == "--axiom-policy=exclude-native-marked" && policy.is_none() {
            policy = Some(AxiomPolicy::ExcludeNativeMarked);
        } else if arg == "--axiom-policy=allow-all-declared-axioms" && policy.is_none() {
            policy = Some(AxiomPolicy::AllowAllDeclaredAxioms);
        } else {
            return Err(InputError::Arguments);
        }
    }
    Ok((declarations, policy.unwrap_or_default()))
}
fn arguments() -> Result<(bool, AxiomPolicy), InputError> {
    arguments_from(std::env::args_os().skip(1))
}
fn main() {
    std::process::exit(run_main());
}

/// Fix glibc's mmap threshold at its initial default and disable
/// its dynamic adjustment, so peak RSS does not depend on which large blocks
/// were freed earlier. Memory layout only: no verdict, charge or report
/// field depends on it, so a failed call (return 0) is ignored.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn pin_glibc_mmap_threshold() {
    use std::os::raw::c_int;
    // glibc `malloc.h`: M_MMAP_THRESHOLD.
    const M_MMAP_THRESHOLD: c_int = -3;
    unsafe extern "C" {
        fn mallopt(param: c_int, value: c_int) -> c_int;
    }
    // SAFETY: `mallopt` is the platform C library's documented tuning call;
    // it takes two integers, retains no pointer and is called once, before
    // any checker thread exists.
    let _ = unsafe { mallopt(M_MMAP_THRESHOLD, 128 * 1024) };
}
#[cfg(not(all(target_os = "linux", target_env = "gnu")))]
fn pin_glibc_mmap_threshold() {}

fn run_main() -> i32 {
    pin_glibc_mmap_threshold();
    // No raw panic payload or attacker-controlled string reaches stderr.
    std::panic::set_hook(Box::new(|_| {}));
    let setup = catch_unwind(|| {
        let arguments = arguments();
        let (declarations, policy) = arguments.unwrap_or_default();
        (Run::new_with_axiom_policy(declarations, policy), arguments)
    });
    let (mut run, arguments) = match setup {
        Ok(setup) => setup,
        // No returned run/buffer exists from which to fabricate a report.
        Err(_) => std::process::exit(3),
    };
    // `Run::check` checks on its own thread, so the writer must be `Send`;
    // the unlocked handle is.
    let mut output = std::io::stdout();
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        if let Err(error) = arguments {
            return run.input_error(error, &mut output);
        }
        if let Some(outcome) = run.bootstrap_error(&mut output) {
            return outcome;
        }
        let Some(path) = std::env::var_os("IN").filter(|path| !path.is_empty()) else {
            return run.input_error(InputError::Io, &mut output);
        };
        let mut input = match std::fs::File::open(path) {
            Ok(input) => input,
            Err(_) => return run.input_error(InputError::Io, &mut output),
        };
        run.check(&mut input, &mut output)
    }))
    .unwrap_or_else(|_| {
        catch_unwind(AssertUnwindSafe(|| run.report_panic(&mut output)))
            .unwrap_or(Outcome::InternalError)
    });
    // Reports have been flushed. Do not run session destructors after publication.
    std::process::exit(exit_code(outcome));
}
