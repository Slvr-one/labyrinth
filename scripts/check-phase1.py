#!/usr/bin/env python3
"""Check the actual extraction and reject a deliberately incorrect parent update."""

import json
import os
import shutil
import subprocess  # nosec B404 -- invokes the pinned compiler toolchain
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLS = Path(os.environ["LABYRINTH_TOOLCHAINS"]).resolve()
ENV = os.environ | {
    "CARGO_HOME": str(TOOLS / "cargo"),
    "RUSTUP_HOME": str(TOOLS / "rustup"),
    "ELAN_HOME": str(TOOLS / "elan"),
    "PATH": os.pathsep.join(
        str(path) for path in (TOOLS / "bin", TOOLS / "cargo/bin", TOOLS / "elan/bin")
    )
    + os.pathsep
    + os.environ["PATH"],
}


def run(args, cwd, *, env=None, expect_failure=False):
    print("+", " ".join(map(str, args)), flush=True)
    result = subprocess.run(  # nosec B603 -- fixed argv, never shell commands
        args,
        cwd=cwd,
        env=ENV if env is None else env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    print(result.stdout, end="", flush=True)
    if not expect_failure:
        result.check_returncode()
    return result


def extract(root):
    run(["charon", "cargo", "--preset=aeneas"], root / "rust")
    run(
        [
            "aeneas",
            "-backend",
            "lean",
            "-split-files",
            "-abort-on-error",
            "-warnings-as-errors",
            "-no-progress-bar",
            "-dest",
            str(root / "lean"),
            "-subdir",
            "LabyrinthCore",
            str(root / "rust/labyrinth_core.llbc"),
        ],
        root,
    )


pins = json.loads((ROOT / "toolchain-pins.json").read_text())
for component in ("charon", "aeneas"):
    revision = run(
        ["git", "rev-parse", "HEAD"], TOOLS / "src" / component
    ).stdout.strip()
    if revision != pins[component]:
        raise SystemExit(f"{component} source revision does not match the pin")
version = run(["aeneas", "-version"], ROOT).stdout.strip()
if version != "aeneas " + pins["aeneas"][:8]:
    raise SystemExit("Aeneas executable does not match the pin")

extract(ROOT)
run(["lake", "build"], ROOT / "lean")
run(["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"], ROOT / "lean")
lean_path = run(["lake", "env", "printenv", "LEAN_PATH"], ROOT / "lean").stdout.strip()

with tempfile.TemporaryDirectory(prefix="labyrinth-negative-") as scratch:
    negative = Path(scratch)
    shutil.copytree(
        ROOT / "rust",
        negative / "rust",
        ignore=shutil.ignore_patterns("target", "*.llbc"),
    )
    source = negative / "rust/src/tree.rs"
    correct = "parents[child] = new_parent;"
    text = source.read_text()
    if text.count(correct) != 1:
        raise SystemExit("Expected exactly one parent-update mutation site")
    source.write_text(text.replace(correct, "parents[child] = child;"))
    (negative / "lean/LabyrinthCore").mkdir(parents=True)
    shutil.copyfile(ROOT / "lean/lean-toolchain", negative / "lean/lean-toolchain")
    shutil.copyfile(
        ROOT / "lean/LabyrinthCore/Spec.lean",
        negative / "lean/LabyrinthCore/Spec.lean",
    )
    extract(negative)
    compiled = negative / "compiled"
    (compiled / "LabyrinthCore").mkdir(parents=True)
    negative_env = ENV | {"LEAN_PATH": str(compiled) + os.pathsep + lean_path}
    for module in ("Types", "Funs"):
        run(
            [
                "lean",
                "-DwarningAsError=true",
                "-o",
                str(compiled / "LabyrinthCore" / f"{module}.olean"),
                f"LabyrinthCore/{module}.lean",
            ],
            negative / "lean",
            env=negative_env,
        )
    result = run(
        ["lean", "-DwarningAsError=true", "LabyrinthCore/Spec.lean"],
        negative / "lean",
        env=negative_env,
        expect_failure=True,
    )
    if result.returncode == 0 or "unsolved goals" not in result.stdout:
        raise SystemExit("Incorrect Rust update was not rejected by the specification")
    print("PASS: incorrect Rust update rejected by the unchanged correspondence proof")
