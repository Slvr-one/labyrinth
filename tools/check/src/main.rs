mod audit;
mod util;

use std::fs;
use std::path::{Path, PathBuf};
use util::{copy_rust_tree, run, Env, TempDir};

const HELP: &str = "\
labyrinth-check: verification gate for the Rust-to-Lean model of labyrinth-core

USAGE (from the repository root):
    LABYRINTH_TOOLCHAINS=<dir> cargo run --release --manifest-path tools/check/Cargo.toml -- \\
        [--root <repo>] [--only <step>]... [--help]

ENVIRONMENT
    LABYRINTH_TOOLCHAINS  required: directory holding src/{charon,aeneas}, bin/, cargo/, rustup/,
                          elan/. CARGO_HOME, RUSTUP_HOME, ELAN_HOME and PATH (bin, cargo/bin,
                          elan/bin first) are set from it for every child process.
                          The tools are assumed installed; nothing is installed or updated.

STEPS (run in this order; all run unless --only is given; the first failure stops the run,
exit status 1; bad usage exits 2; each check prints a PASS line):
  pins            reads toolchain-pins.json; `git rev-parse HEAD` in $LABYRINTH_TOOLCHAINS/src/charon
                  and /src/aeneas must equal the pinned revisions; `aeneas -version` must print
                  `aeneas <first 8 characters of the aeneas pin>`.
  extraction      in rust/: charon cargo --preset=aeneas
                    --include=core::slice::{impl core::default::Default for &Slice<_>}::default
                    --include=core::option::{impl core::default::Default for core::option::Option<_>}::default
                    --include=core::result::_::is_err
                  then aeneas -backend lean -split-files -abort-on-error -warnings-as-errors
                    -no-progress-bar -all-computable -dest <tmp> -subdir LabyrinthCore
                    rust/labyrinth_core.llbc
                  checks: generated FunsExternal_Template.lean declares exactly the eight modeled
                  externals (alloc.vec.Vec.clear, core.num.I32.abs, core.num.I32.rem_euclid,
                  core.ops.range.RangeInclusive.contains, core.option.Option.Insts.CoreCloneClone.clone,
                  core.option.Option.Insts.CoreCmpPartialEqOption.eq,
                  core.option.Option.Insts.CoreFmtDebug.fmt, core.option.OptionShared0T.copied);
                  generated Types.lean and Funs.lean declare no axiom (see repo-externals); both
                  are byte-identical to lean/LabyrinthCore/{Types,Funs}.lean. The checked-in files
                  are never overwritten.
  repo-externals  lean/LabyrinthCore/FunsExternal.lean declares no axiom: no line whose first token,
                  after any `@[...]` attributes and private/protected/noncomputable/unsafe/partial/
                  nonrec modifiers, is the keyword `axiom`.
  kernel-check    no file under lean/ (outside lean/.lake) contains `skipKernelTC` or
                  `addDeclWithoutChecking`: the option and the API that add declarations without
                  kernel type checking.
  build           lake build in lean/ (warnings are errors via the lakefile).
  audit           `lake env lean -DwarningAsError=true Audit.lean` in lean/. The `#print axioms <ident>`
                  lines of Audit.lean are the expected roots (non-empty, no duplicates). The output
                  must contain exactly one `'<root>' depends on axioms: [...]` or `'<root>' does not
                  depend on any axioms` entry per root: no duplicate, missing or unlisted root,
                  no stray text, and only propext, Classical.choice, Quot.sound as axioms. Names are
                  parsed from the fixed suffixes, so any Lean identifier (`'`, `?`, dots) works.
                  Assumes `build` has run.
  axiom-guard     negative fixture: in a temp dir, a theorem proved from `axiom unapproved_axiom`
                  must be rejected by the same audit policy with exactly that axiom reported.
  mutation        negative: copy rust/ (without target and *.llbc) to a temp dir; require exactly one
                  `parents[child] = new_parent;` in src/tree.rs and replace it with
                  `parents[child] = child;`; extract that copy with the same flags into the temp lean
                  dir; compile Types, FunsExternal, Funs there; the unchanged Spec.lean must then fail
                  to elaborate with `unsolved goals`.

OPTIONS
    --only <step>   run only this step (repeatable; steps still run in the order above)
    --root <repo>   repository root (default: current directory)
    --help          this text
";

const STEPS: [&str; 8] = [
    "pins",
    "extraction",
    "repo-externals",
    "kernel-check",
    "build",
    "audit",
    "axiom-guard",
    "mutation",
];

const CHARON_ARGS: [&str; 5] = [
    "cargo",
    "--preset=aeneas",
    "--include=core::slice::{impl core::default::Default for &Slice<_>}::default",
    "--include=core::option::{impl core::default::Default for core::option::Option<_>}::default",
    "--include=core::result::_::is_err",
];

const EXPECTED_EXTERNALS: [&str; 8] = [
    "alloc.vec.Vec.clear",
    "core.num.I32.abs",
    "core.num.I32.rem_euclid",
    "core.ops.range.RangeInclusive.contains",
    "core.option.Option.Insts.CoreCloneClone.clone",
    "core.option.Option.Insts.CoreCmpPartialEqOption.eq",
    "core.option.Option.Insts.CoreFmtDebug.fmt",
    "core.option.OptionShared0T.copied",
];

const DECLARATION_MODIFIERS: [&str; 6] = [
    "private",
    "protected",
    "noncomputable",
    "unsafe",
    "partial",
    "nonrec",
];

const KERNEL_BYPASSES: [&str; 2] = ["skipKernelTC", "addDeclWithoutChecking"];

type Res = Result<(), String>;

struct Ctx {
    root: PathBuf,
    tools: PathBuf,
    env: Env,
}

fn main() {
    let mut only: Vec<String> = Vec::new();
    let mut root = PathBuf::from(".");
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                print!("{HELP}");
                return;
            }
            "--only" => match args.next() {
                Some(step) if STEPS.contains(&step.as_str()) => only.push(step),
                other => usage(&format!(
                    "--only needs one of {}, got {other:?}",
                    STEPS.join(", ")
                )),
            },
            "--root" => match args.next() {
                Some(path) => root = PathBuf::from(path),
                None => usage("--root needs a path"),
            },
            other => usage(&format!("unknown argument {other:?}")),
        }
    }
    let ctx = match Ctx::new(&root) {
        Ok(ctx) => ctx,
        Err(message) => fail(&message),
    };
    for step in STEPS
        .iter()
        .filter(|s| only.is_empty() || only.iter().any(|o| o == *s))
    {
        println!("== {step}");
        let result = match *step {
            "pins" => ctx.pins(),
            "extraction" => ctx.extraction(),
            "repo-externals" => ctx.repo_externals(),
            "kernel-check" => ctx.kernel_check(),
            "build" => ctx.build(),
            "audit" => ctx.audit(),
            "axiom-guard" => ctx.axiom_guard(),
            _ => ctx.mutation(),
        };
        if let Err(message) = result {
            fail(&format!("{step}: {message}"));
        }
    }
}

fn usage(message: &str) -> ! {
    eprintln!("error: {message}\n(see --help)");
    std::process::exit(2);
}

fn fail(message: &str) -> ! {
    eprintln!("FAIL: {message}");
    std::process::exit(1);
}

fn read(path: &Path) -> Result<String, String> {
    fs::read_to_string(path).map_err(|e| format!("cannot read {}: {e}", path.display()))
}

fn write(path: &Path, text: &str) -> Res {
    fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
}

fn s(path: &Path) -> &str {
    path.to_str().expect("paths are UTF-8")
}

/// `text` without its leading `word`, when `word` is a whole token there.
fn keyword<'a>(text: &'a str, word: &str) -> Option<&'a str> {
    text.strip_prefix(word).filter(|rest| {
        rest.chars()
            .next()
            .is_none_or(|c| !(c.is_alphanumeric() || c == '_'))
    })
}

/// The text after a line's leading `axiom` keyword, past `@[...]` attributes and modifiers.
fn axiom_declaration(line: &str) -> Option<&str> {
    let mut rest = line.trim_start();
    loop {
        if let Some(attributes) = rest.strip_prefix("@[") {
            let mut depth = 1usize;
            let end = attributes.char_indices().find_map(|(i, c)| {
                match c {
                    '[' => depth += 1,
                    ']' => depth -= 1,
                    _ => {}
                }
                (depth == 0).then_some(i + 1)
            })?;
            rest = attributes[end..].trim_start();
        } else if let Some(after) = DECLARATION_MODIFIERS
            .iter()
            .find_map(|modifier| keyword(rest, modifier))
        {
            rest = after.trim_start();
        } else {
            return keyword(rest, "axiom");
        }
    }
}

fn declares_axiom(text: &str) -> bool {
    text.lines().any(|line| axiom_declaration(line).is_some())
}

fn external_names(template: &str) -> Vec<String> {
    let mut names: Vec<String> = template
        .lines()
        .filter_map(axiom_declaration)
        .filter_map(|rest| rest.split_whitespace().next())
        .map(str::to_owned)
        .collect();
    names.sort();
    names
}

/// The first kernel-check bypass named in `text`, matched anywhere including comments.
fn kernel_bypass(text: &str) -> Option<&'static str> {
    KERNEL_BYPASSES
        .into_iter()
        .find(|bypass| text.contains(bypass))
}

/// Files under `dir`, skipping `.lake` build and dependency directories.
fn lean_tree_files(dir: &Path, files: &mut Vec<PathBuf>) -> Res {
    let entries = fs::read_dir(dir).map_err(|e| format!("cannot list {}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.is_dir() {
            if path.file_name() != Some(".lake".as_ref()) {
                lean_tree_files(&path, files)?;
            }
        } else {
            files.push(path);
        }
    }
    Ok(())
}

impl Ctx {
    fn new(root: &Path) -> Result<Self, String> {
        let root = root
            .canonicalize()
            .map_err(|e| format!("bad root {}: {e}", root.display()))?;
        if !root.join("toolchain-pins.json").is_file() {
            return Err(format!(
                "{} is not the repository root (no toolchain-pins.json)",
                root.display()
            ));
        }
        let tools = std::env::var_os("LABYRINTH_TOOLCHAINS")
            .ok_or("LABYRINTH_TOOLCHAINS must name the isolated toolchain directory")?;
        let tools = Path::new(&tools)
            .canonicalize()
            .map_err(|e| format!("bad LABYRINTH_TOOLCHAINS: {e}"))?;
        let path = [
            tools.join("bin"),
            tools.join("cargo/bin"),
            tools.join("elan/bin"),
        ]
        .iter()
        .map(|p| s(p).to_owned())
        .chain(std::env::var("PATH"))
        .collect::<Vec<_>>()
        .join(":");
        let mut env: Env = std::env::vars().collect();
        env.retain(|(k, _)| {
            !["CARGO_HOME", "RUSTUP_HOME", "ELAN_HOME", "PATH"].contains(&k.as_str())
        });
        env.push(("CARGO_HOME".into(), s(&tools.join("cargo")).into()));
        env.push(("RUSTUP_HOME".into(), s(&tools.join("rustup")).into()));
        env.push(("ELAN_HOME".into(), s(&tools.join("elan")).into()));
        env.push(("PATH".into(), path));
        Ok(Self { root, tools, env })
    }

    fn run(&self, program: &str, args: &[&str], cwd: &Path) -> Result<String, String> {
        run(program, args, cwd, &self.env, false).map(|o| o.text)
    }

    fn lean_dir(&self) -> PathBuf {
        self.root.join("lean")
    }

    fn pins(&self) -> Res {
        let pins: serde_json::Value =
            serde_json::from_str(&read(&self.root.join("toolchain-pins.json"))?)
                .map_err(|e| format!("toolchain-pins.json: {e}"))?;
        let pin = |key: &str| {
            pins[key]
                .as_str()
                .map(str::to_owned)
                .ok_or(format!("toolchain-pins.json lacks {key}"))
        };
        for component in ["charon", "aeneas"] {
            let revision = self.run(
                "git",
                &["rev-parse", "HEAD"],
                &self.tools.join("src").join(component),
            )?;
            if revision.trim() != pin(component)? {
                return Err(format!(
                    "{component} source revision does not match the pin"
                ));
            }
            println!("PASS: {component} source revision matches the pin");
        }
        let version = self.run("aeneas", &["-version"], &self.root)?;
        if version.trim() != format!("aeneas {}", &pin("aeneas")?[..8]) {
            return Err("Aeneas executable does not match the pin".into());
        }
        println!("PASS: aeneas -version matches the pin");
        Ok(())
    }

    /// Charon then Aeneas on `root/rust`, writing `<destination>/LabyrinthCore`; checks the
    /// external template and the absence of generated axioms.
    fn extract(&self, root: &Path, destination: &Path) -> Res {
        self.run("charon", &CHARON_ARGS, &root.join("rust"))?;
        let llbc = root.join("rust/labyrinth_core.llbc");
        self.run(
            "aeneas",
            &[
                "-backend",
                "lean",
                "-split-files",
                "-abort-on-error",
                "-warnings-as-errors",
                "-no-progress-bar",
                "-all-computable",
                "-dest",
                s(destination),
                "-subdir",
                "LabyrinthCore",
                s(&llbc),
            ],
            root,
        )?;
        let generated = destination.join("LabyrinthCore");
        let names = external_names(&read(&generated.join("FunsExternal_Template.lean"))?);
        if names != EXPECTED_EXTERNALS {
            return Err(format!(
                "Extraction external templates differ from the modeled set: {names:?}"
            ));
        }
        println!("PASS: external template declares exactly the modeled set");
        for module in ["Types.lean", "Funs.lean"] {
            if declares_axiom(&read(&generated.join(module))?) {
                return Err(format!("Generated {module} declares an axiom"));
            }
        }
        println!("PASS: generated Types.lean and Funs.lean declare no axiom");
        Ok(())
    }

    fn extraction(&self) -> Res {
        let temp = TempDir::new("labyrinth-model-")?;
        self.extract(&self.root, temp.path())?;
        for module in ["Types.lean", "Funs.lean"] {
            let checked_in = self.root.join("lean/LabyrinthCore").join(module);
            let generated = temp.path().join("LabyrinthCore").join(module);
            let read_bytes =
                |p: &Path| fs::read(p).map_err(|e| format!("cannot read {}: {e}", p.display()));
            if read_bytes(&generated)? != read_bytes(&checked_in)? {
                return Err(format!("Generated Lean differs from checked-in {module}"));
            }
        }
        println!("PASS: generated Types.lean and Funs.lean match the checked-in files");
        Ok(())
    }

    fn repo_externals(&self) -> Res {
        if declares_axiom(&read(
            &self.root.join("lean/LabyrinthCore/FunsExternal.lean"),
        )?) {
            return Err("Repo FunsExternal.lean declares an axiom".into());
        }
        println!("PASS: repo FunsExternal.lean declares no axiom");
        Ok(())
    }

    fn kernel_check(&self) -> Res {
        let mut files = Vec::new();
        lean_tree_files(&self.lean_dir(), &mut files)?;
        files.sort();
        for file in &files {
            if let Some(bypass) = kernel_bypass(&read(file)?) {
                return Err(format!("{} contains `{bypass}`", file.display()));
            }
        }
        println!(
            "PASS: no kernel-check bypass in {} files under lean/",
            files.len()
        );
        Ok(())
    }

    fn build(&self) -> Res {
        self.run("lake", &["build"], &self.lean_dir())?;
        println!("PASS: lake build");
        Ok(())
    }

    fn audit(&self) -> Res {
        let expected = audit::expected_roots(&read(&self.root.join("lean/Audit.lean"))?);
        let distinct: std::collections::BTreeSet<_> = expected.iter().collect();
        if expected.is_empty() || distinct.len() != expected.len() {
            return Err("The axiom audit must list distinct production theorems".into());
        }
        let output = self.run(
            "lake",
            &["env", "lean", "-DwarningAsError=true", "Audit.lean"],
            &self.lean_dir(),
        )?;
        let count = audit::check(&output, &expected).map_err(|e| e.to_string())?;
        println!("PASS: axiom audit, {count} roots audited");
        Ok(())
    }

    fn axiom_guard(&self) -> Res {
        let scratch = TempDir::new("labyrinth-guard-")?;
        let lean = scratch.path().join("lean");
        fs::create_dir(&lean).map_err(|e| e.to_string())?;
        self.copy_lean_toolchain(&lean)?;
        let output = self.guard_fixture(&lean)?;
        Self::require_guard(&output)
    }

    fn copy_lean_toolchain(&self, lean: &Path) -> Res {
        fs::copy(
            self.root.join("lean/lean-toolchain"),
            lean.join("lean-toolchain"),
        )
        .map(drop)
        .map_err(|e| format!("cannot copy lean-toolchain: {e}"))
    }

    fn guard_fixture(&self, lean: &Path) -> Result<String, String> {
        write(
            &lean.join("AxiomGuard.lean"),
            "axiom unapproved_axiom : False\n\
             theorem set_parent_spec : True := False.elim unapproved_axiom\n\
             #print axioms set_parent_spec\n",
        )?;
        self.run("lean", &["-DwarningAsError=true", "AxiomGuard.lean"], lean)
    }

    fn require_guard(output: &str) -> Res {
        match audit::check(output, &["set_parent_spec".to_owned()]) {
            Err(audit::AuditError::Unexpected(names)) if names == ["unapproved_axiom"] => {
                println!("PASS: application-defined axiom rejected by allowlist");
                Ok(())
            }
            Err(other) => Err(format!("axiom guard failed for another reason: {other}")),
            Ok(_) => Err("Application-defined axiom was not rejected".into()),
        }
    }

    fn mutation(&self) -> Res {
        let lean_path = self.run("lake", &["env", "printenv", "LEAN_PATH"], &self.lean_dir())?;
        let lean_path = lean_path.trim();
        let scratch = TempDir::new("labyrinth-negative-")?;
        let negative = scratch.path();
        copy_rust_tree(&self.root.join("rust"), &negative.join("rust"))
            .map_err(|e| format!("cannot copy rust/: {e}"))?;
        let source = negative.join("rust/src/tree.rs");
        let correct = "parents[child] = new_parent;";
        let text = read(&source)?;
        if text.matches(correct).count() != 1 {
            return Err("Expected exactly one parent-update mutation site".into());
        }
        write(&source, &text.replace(correct, "parents[child] = child;"))?;
        let lean = negative.join("lean");
        fs::create_dir_all(lean.join("LabyrinthCore")).map_err(|e| e.to_string())?;
        self.copy_lean_toolchain(&lean)?;
        for file in ["Spec.lean", "FunsExternal.lean"] {
            let from = self.root.join("lean/LabyrinthCore").join(file);
            fs::copy(&from, lean.join("LabyrinthCore").join(file))
                .map_err(|e| format!("cannot copy {file}: {e}"))?;
        }
        self.extract(negative, &lean)?;
        let compiled = negative.join("compiled");
        fs::create_dir_all(compiled.join("LabyrinthCore")).map_err(|e| e.to_string())?;
        let mut env = self.env.clone();
        env.push(("LEAN_PATH".into(), format!("{}:{lean_path}", s(&compiled))));
        for module in ["Types", "FunsExternal", "Funs"] {
            let olean = compiled
                .join("LabyrinthCore")
                .join(format!("{module}.olean"));
            let source = format!("LabyrinthCore/{module}.lean");
            run(
                "lean",
                &["-DwarningAsError=true", "-o", s(&olean), &source],
                &lean,
                &env,
                false,
            )?;
        }
        let result = run(
            "lean",
            &["-DwarningAsError=true", "LabyrinthCore/Spec.lean"],
            &lean,
            &env,
            true,
        )?;
        if result.code == 0 || !result.text.contains("unsolved goals") {
            return Err("Incorrect Rust update was not rejected by the specification".into());
        }
        println!("PASS: incorrect Rust update rejected by the unchanged correspondence proof");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn axiom_declarations_are_whole_keywords_at_line_start() {
        assert!(declares_axiom("def x := 1\naxiom foo : False\n"));
        assert!(declares_axiom("  axiom foo : False"));
        assert!(!declares_axiom("def axiomatic := 1\n-- axiom foo\n"));
        assert!(!declares_axiom(
            "/- private axiom foo -/\ntheorem axiom_free : True := trivial\n"
        ));
        assert!(!declares_axiom(
            "private def axiom_like := 1\nprivate axiomatic : Nat\n"
        ));
    }

    #[test]
    fn axiom_declarations_after_modifiers_and_attributes_are_found() {
        for line in [
            "private axiom foo : False",
            "protected axiom foo : False",
            "noncomputable axiom foo : Nat",
            "unsafe axiom foo : False",
            "partial axiom foo : False",
            "nonrec axiom foo : False",
            "@[simp] axiom foo : False",
            "  @[simp, reducible] @[instance] private noncomputable axiom foo : Nat",
            "@[implemented_by f [x]] axiom foo : Nat",
        ] {
            assert!(declares_axiom(line), "{line}");
        }
        assert!(!declares_axiom(
            "@[simp] theorem axiom_free : True := trivial"
        ));
        assert!(!declares_axiom("@[simp axiom foo : False"));
    }

    #[test]
    fn kernel_bypasses_are_rejected() {
        assert_eq!(
            kernel_bypass("set_option debug.skipKernelTC true in\ntheorem t : True := trivial\n"),
            Some("skipKernelTC")
        );
        assert_eq!(
            kernel_bypass("moreLeanArgs = [\"-Ddebug.skipKernelTC=true\"]\n"),
            Some("skipKernelTC")
        );
        assert_eq!(
            kernel_bypass("#eval Lean.Environment.addDeclWithoutChecking env decl\n"),
            Some("addDeclWithoutChecking")
        );
        assert_eq!(kernel_bypass("set_option maxRecDepth 4096 in\n"), None);
    }

    #[test]
    fn template_names_are_sorted() {
        let template =
            "axiom b.c : Nat\ndef x := 1\naxiom a.b {T : Type} : T\nprivate axiom c.d : Nat\n";
        assert_eq!(external_names(template), ["a.b", "b.c", "c.d"]);
    }
}
