#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# ///
"""Create a deterministic, anonymized code-submission ZIP archive."""

from __future__ import annotations

import argparse
import os
import shutil
import stat
import subprocess
import tempfile
import zipfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_ROOT = "lean-mechanization"
DEFAULT_OUTPUT = ROOT / "dist" / "lean-mechanization.zip"

def run_git(*args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def submission_files() -> list[Path]:
    """Return tracked and non-ignored untracked files from the current tree."""
    raw = run_git("ls-files", "--cached", "--others", "--exclude-standard", "-z")
    return [Path(item.decode()) for item in raw.split(b"\0") if item]


def excluded(path: Path, output: Path) -> bool:
    if path.parts and path.parts[0] == "scripts":
        return True
    if path.suffix.lower() == ".pdf":
        return True
    if path.name == ".DS_Store":
        return True
    try:
        return (ROOT / path).resolve() == output.resolve()
    except FileNotFoundError:
        return False


def copy_worktree(stage: Path, output: Path) -> None:
    for relative in submission_files():
        source = ROOT / relative
        if excluded(relative, output) or not source.exists():
            continue
        destination = stage / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if source.is_symlink():
            destination.symlink_to(os.readlink(source))
        else:
            shutil.copy2(source, destination)


def configured_git_email() -> str | None:
    result = subprocess.run(
        ["git", "-C", str(ROOT), "config", "user.email"],
        check=False,
        stdout=subprocess.PIPE,
        text=True,
    )
    email = result.stdout.strip()
    return email or None


def verify_anonymized(stage: Path) -> None:
    forbidden = {
        str(ROOT): "repository path",
        str(Path.home()): "home-directory path",
    }
    if email := configured_git_email():
        forbidden[email] = "configured Git email"

    leaks: list[str] = []
    for path in stage.rglob("*"):
        if not path.is_file():
            continue
        try:
            text = path.read_text()
        except UnicodeDecodeError:
            continue
        for needle, description in forbidden.items():
            if needle and needle in text:
                leaks.append(f"{path.relative_to(stage)}: {description}")

    pdfs = list(stage.rglob("*.pdf")) + list(stage.rglob("*.PDF"))
    leaks.extend(f"{path.relative_to(stage)}: PDF included" for path in pdfs)
    if leaks:
        formatted = "\n".join(f"  - {leak}" for leak in sorted(set(leaks)))
        raise RuntimeError(f"anonymization checks failed:\n{formatted}")


def write_archive(stage: Path, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.unlink(missing_ok=True)
    with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(stage.rglob("*")):
            if not path.is_file():
                continue
            relative = Path(ARCHIVE_ROOT) / path.relative_to(stage)
            info = zipfile.ZipInfo(str(relative), date_time=(1980, 1, 1, 0, 0, 0))
            mode = path.stat().st_mode
            permissions = 0o755 if mode & stat.S_IXUSR else 0o644
            info.external_attr = (stat.S_IFREG | permissions) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, path.read_bytes())
    temporary.replace(output)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help=f"output ZIP path (default: {DEFAULT_OUTPUT.relative_to(ROOT)})",
    )
    args = parser.parse_args()
    output = args.output if args.output.is_absolute() else ROOT / args.output

    with tempfile.TemporaryDirectory(prefix="lw-rust-anonymous-") as temporary:
        stage = Path(temporary)
        copy_worktree(stage, output)
        verify_anonymized(stage)
        write_archive(stage, output)

    print(output)


if __name__ == "__main__":
    main()
