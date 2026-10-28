# Offline field capture

This directory is the complete typed support for lane
`ao.fleet.dynamic.0794c03c15cd`.

It provides a deterministic, network-free field inspection capture format.
It does not depend on DASHI Agda surfaces and it does not modify any ESD
surface.

## Contract

A capture contains exactly:

- `manifest.json`
- `payload/`

The manifest uses `dashi-offline-capture/v1`.
Each payload file has a relative POSIX path, byte size, and SHA-256 digest.
The manifest also stores a SHA-256 digest of the canonical sorted file-entry
list.

The tool rejects:

- symlink sources or symlink entries
- non-regular source entries
- a destination inside the source tree
- an existing destination
- unsafe or duplicate manifest paths
- payload files missing from the manifest
- manifest files missing from the payload
- size or SHA-256 mismatches
- non-canonical manifest ordering

The capture contains no clock value, host path, hostname, user name, or network
result. The same bytes and label therefore produce the same manifest.

## Capture

```sh
python inspection/offline-capture/offline_capture.py capture \
  /path/to/source \
  /path/to/capture \
  --label field-run-001
```

The command prints a compact JSON summary.

## Verify

```sh
python inspection/offline-capture/offline_capture.py verify \
  /path/to/capture
```

Verification succeeds only when the payload path set, sizes, hashes, ordering,
and manifest content digest all match.

## Deterministic regression

```sh
python inspection/offline-capture/test_offline_capture.py
```

The regression covers deterministic recapture, byte preservation, single-file
capture, tamper detection, unexpected-file detection, manifest-order
enforcement, destination containment rejection, and symlink rejection.

## Lane invariants

- Typed support is only `inspection/offline-capture`.
- The implementation performs no network I/O.
- The implementation contains no Agda trust escape.
- The implementation does not edit `dashi_digital_esd`, `*digital_esd*`,
  or `*ESD*`.
- Capture identity is content-derived.
- Verification is fail-closed.
