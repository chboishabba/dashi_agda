# Monster 10-Walk Intake

Purpose: record the exact upstream source and the current local interpretation
used when `dashi_agda` references the Monster 10-walk / 10-basin discussion.

## Source hierarchy

Use these sources in order:

1. Upstream source material in the pinned `monster/` checkout:
   - `monster/experiments/bott_periodicity/monster_walk.tex`
   - the key table starts at the "The 10 Groups" section and lists the ten
     sequences:
     `8080, 1742, 479, 451, 2875, 8864, 5990, 496, 1710, 7570`
2. Local executable/canonical interpretation in the sibling repo:
   - `../FRACDASH/MONSTER10WALK_CANONICAL.md`
3. Local handoff/claim-boundary note in the sibling repo:
   - `../FRACDASH/JMD_HANDOFF_NOTE.md`

## What this repo should assume

- The upstream `monster` repo is the source of the 10-group / 10-walk material.
- `FRACDASH` is the source of the current local executable lock and
  claim-boundary language.
- `dashi_agda` should treat both as intake context unless and until a
  corresponding Agda formalization is added here.

## Current safe reading

- The ten groups in `monster_walk.tex` are the relevant source table for the
  "10 basins" thread.
- The current local canonical walk is the strict sequence order
  `0 -> 1 -> 2 -> ... -> 9` frozen in `FRACDASH`.
- The local chain/rank proxy of `4` belongs to that FRACDASH canonicalization.
- Stronger statements about full basin semantics, root-system identity, or a
  completed theorem closure should stay outside `dashi_agda` unless formalized
  here directly.

## Why keep the submodule

- The upstream source is not just the README; the cited material lives in
  `experiments/bott_periodicity/monster_walk.tex`.
- Pinning `monster/` as a submodule keeps the citation stable and avoids
  re-copying a large, moving upstream repository into local docs.
