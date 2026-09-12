#!/usr/bin/env python3
"""Discard only the standard, worktree-local validation scratch directories."""

from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parent.parent
DIRECTORIES = (
    "validation",
    "validation-direct-lcnf",
    "validation-v8",
    "validation-comparison-attestations",
    "validation-coverage",
)


def clean(root: Path = ROOT) -> None:
    build = root / "_build"
    targets = [build / name for name in DIRECTORIES]
    # Validate the whole set before deleting anything. Do not follow a staging
    # symlink or remove files that have become source-controlled.
    if build.is_symlink():
        raise ValueError("refusing symlinked _build")
    for path in targets:
        if path.is_symlink() or (path.exists() and not path.is_dir()):
            raise ValueError(f"refusing non-directory validation scratch: {path}")
    tracked = subprocess.check_output(
        ["git", "ls-files", "-z", "--", *[str(p.relative_to(root)) for p in targets]],
        cwd=root,
    )
    if tracked:
        raise ValueError("refusing to remove tracked validation files")
    for path in targets:
        if path.exists():
            shutil.rmtree(path)
            print(f"removed disposable scratch: {path.relative_to(root)}", flush=True)


if __name__ == "__main__":
    clean()
