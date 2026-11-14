#!/usr/bin/env python3
"""Atomic, no-clobber publication of immutable content-addressed spool entries.

A reader only opens the final filename. An in-flight writer uses a private
temporary inode in the same directory, fsyncs, and publishes with hard-link
creation, which fails without replacing an existing entry. POSIX filesystem
semantics are required; NFS/cloud-backed mounts need separate validation.
"""
from __future__ import annotations
import os
import tempfile
from pathlib import Path

class PublicationError(ValueError):
    pass

def _fsync_directory(directory: Path) -> None:
    fd = os.open(directory, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(fd)
    finally:
        os.close(fd)

def publish_immutable(path: Path, expected: bytes) -> bool:
    """Return True for a new entry, False for identical existing bytes.

    Never permit replacing mismatched bytes, and never expose partial final
    files. The caller must ensure the spool is a trusted, private directory.
    """
    path = Path(path)
    directory = path.parent
    if not directory.is_dir() or directory.is_symlink():
        raise PublicationError("unsafe spool directory")
    if not isinstance(expected, bytes) or not expected:
        raise PublicationError("empty immutable entry")
    fd, tmp = tempfile.mkstemp(prefix=".staging-", dir=directory)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(expected)
            out.flush()
            os.fsync(out.fileno())
        try:
            os.link(tmp, path, follow_symlinks=False)
            created = True
            _fsync_directory(directory)
        except FileExistsError:
            created = False
        if path.is_symlink() or not path.is_file() or path.read_bytes() != expected:
            raise PublicationError("conflicting or incomplete immutable entry")
        return created
    finally:
        os.unlink(tmp)
