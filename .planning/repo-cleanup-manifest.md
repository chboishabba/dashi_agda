# Repo Cleanup Manifest

Snapshot date: `2026-06-02`

Declared surface level: `inventory`.

This manifest is Pass 0 of the repo cleanup plan. It classifies the current
repo surfaces before any move, archive, untrack, or Agda module reorganization.

## Scope

In scope:

- current repo: `/home/c/Documents/code/dashi_agda`
- root files and generated-looking tracked files
- `DASHI/` formal tree
- `Docs/`, `.planning/`, `scripts/`, `tests/`
- import-map preparation for future index modules

Out of scope for cleanup mutation:

- `DCHoTT-Agda/`
- `cubical/`
- `Monster-LILA/`
- `monster/`
- sibling repos such as `../dashiCFD`, `../dashiRTX`, `../dashifine`,
  `../DASHIg`, and `../dashi_lean4`

## Worktree State

Branch:

```text
work/post-checkpoint-2026-05-01...origin/work/post-checkpoint-2026-05-01
```

Existing dirty state at inventory time:

```text
M CHANGELOG.md
M DASHI/Everything.agda
M DASHI/Physics/Closure/PublishableFullUnificationStackReceipt.agda
M Docs/ClayNSProofRoadmap.md
M Docs/CompleteVerifiedPhysicsUnificationRoadmap.md
M TODO.md
M devlog.md
M status.md
?? DASHI/Physics/Closure/ITIRPNFPressureUnificationSupportReceipt.agda
?? DASHI/Physics/Closure/KeyTermCorrespondenceIndexReceipt.agda
?? DASHI/Physics/Closure/LocalDocs369UnificationSupportReceipt.agda
?? DASHI/Physics/Closure/NSTailFluxIdentityAnalyticTargetReceipt.agda
?? DASHI/Physics/Closure/SiblingCodecFiningContinuousSupportReceipt.agda
?? DASHI/Physics/Closure/UniversalScaleGraphBarrierTargetReceipt.agda
?? Docs/RepoStructureCleanupRoadmap.md
?? ROOT_INDEX.md
```

Cleanup work must not revert or overwrite those unrelated dirty changes.

## Tracked File Pressure

Top tracked directories:

```text
2191 DASHI
 382 Docs
 306 scripts
 186 .autonomous-orchestrator
 176 Ontology
  42 da51_shards
  37 temp-DOWNLOADED
  31 .planning
  26 logs
```

Tracked `DASHI/` namespace pressure:

```text
1847 DASHI/Physics
 114 DASHI/Geometry
  47 DASHI/Algebra
  42 DASHI/Arithmetic
  21 DASHI/Combinatorics
  16 DASHI/Interop
  13 DASHI/Biology
  10 DASHI/Reasoning
```

Main pressure point:

```text
DASHI/Physics/Closure direct .agda files: 1190
DASHI/Physics/Closure total .agda files: 1391
```

Candidate future index lanes by filename scan:

```text
Margin      11
NS          94
YM          81
Gate3       31
Programme   62
Authority  108
```

These counts are candidate-routing aids only. They are not proof of final lane
membership.

## Submodule Boundaries

Configured submodules:

```text
DCHoTT-Agda  https://github.com/felixwellen/DCHoTT-Agda.git
Monster-LILA https://github.com/meta-introspector/Monster-LILA.git
cubical      https://github.com/agda/cubical.git
monster      https://github.com/meta-introspector/monster.git
```

Observed recursive submodule issue:

```text
fatal: no submodule mapping found in .gitmodules for path 'diffusion-rs'
fatal: failed to recurse into submodule 'monster'
```

This is recorded as submodule hygiene noise. It is not part of the first cleanup
pass.

## Root Classification

Keep live at root:

- `README.md`
- `README.agda.md`
- `ROOT_INDEX.md`
- `architecture.md`
- `spec.md`
- `plan.md`
- `status.md`
- `TODO.md`
- `CHANGELOG.md`
- `devlog.md`
- `dashi-agda.agda-lib`
- `flake.nix`
- `flake.lock`
- `.gitignore`
- `.gitmodules`

Submodule roots at root:

- `DCHoTT-Agda`
- `Monster-LILA`
- `cubical`
- `monster`

Top-level legacy Agda modules:

- `ActionMonotonicity.agda`
- `AntiFascistSystem.agda`
- `Base369.agda`
- `CRTJFixedPointBridge.agda`
- `CRTPeriod.agda`
- `Contraction.agda`
- `CounterexampleHarness.agda`
- `DASHI_Tests.agda`
- `Fascism_Tests.agda`
- `FascisticContractionBridge.agda`
- `FascisticSystem.agda`
- `FixedPoint.agda`
- `HGSA_Fixpoints.agda`
- `JFixedPoint.agda`
- `LogicTlurey.agda`
- `MaassRestoration.agda`
- `MonsterConformance.agda`
- `MonsterGroups.agda`
- `MonsterOntos.agda`
- `MonsterSpec.agda`
- `MonsterState.agda`
- `MonsterTraceCounts.agda`
- `MonsterVectors.agda`
- `Moonshine.agda`
- `MoonshineEarn.agda`
- `Overflow.agda`
- `PerfHistory.agda`
- `PrimeRoles.agda`
- `SWAR_Equivalence.agda`
- `TenfoldBridges.agda`
- `ThreeAdic_Attractor.agda`
- `UFTC_Lattice.agda`
- `Ultrametric.agda`
- `Z6_RegularInverse.agda`

These are high-risk physical move candidates because imports are path-sensitive.
Do not move them in Pass 1.

## Generated-Looking And Evidence-Shard Tracked Classes

Counts:

```text
all_code*.txt                              37
status.paper7*.root-validation.log         9
temp-DOWNLOADED tracked paths              37
tracked *.agdai                             1
.cache/*.tsv tracked                        3
da51_shards tracked files                  42
```

Specific root generated/scratch candidates:

- `Book.pdf`
- `TEST_ADD_FILE.tmp`
- `all_code*.txt`
- `gitignore pls ignorefucken hearbeats man.7z`
- `status.paper7-wave*.root-validation.log`

DA51 boundary:

- `da51_shards/` is not currently recorded by Git as a submodule.
- Git records its files as regular tracked files (`100644`), not a gitlink.
- There is no nested `da51_shards/.git` and no `.gitmodules` entry for it.
- GitHub search under `meta-introspector` did not find the literal path name
  `da51_shards`, but did find the DA51 shard convention in
  `meta-introspector/dashi_lean4` and `meta-introspector/erdfa-publish`.
- The upstream/meta-introspector convention uses generated Lean wrappers from
  `/tmp/dashi_shards/*.cbor`, with `da51Tag = 55889` (`0xDA51`) and proofs such
  as `shard_0_is_da51`.
- Local evidence matches that bridge: `perf_da51.py` emits DA51 CBOR shards into
  `da51_shards/`, and `PerfHistory.agda` says it was generated from that shard
  directory.
- Treat `da51_shards/` as tracked DA51 evidence/runtime shard material until a
  separate provenance pass proves it is generated, reproducible, and safe to
  archive or untrack.
- `agda_da51_source.jsonl` and `agda_da51_traces.jsonl` are root DA51 trace
  snapshots. They should be indexed with the DA51 shard surface, not cleaned as
  generic junk.

MAlonzo boundary:

- `MAlonzo/` is not tracked by Git in this checkout.
- `.gitignore` explicitly ignores `MAlonzo/`.
- The directory currently contains generated Agda-to-Haskell output and build
  products (`.hs`, `.hi`, `.o`) and is about `13M` / `1112` files.
- `scripts/materialize_profile_summary_family.hs` imports generated
  `MAlonzo.Code.*` modules, so deleting `MAlonzo/` is operationally safe only
  when the generated Haskell output can be rebuilt for that workflow.
- Treat `MAlonzo/` as ignored local build/runtime output, not as source, not as
  a submodule, and not as an archive candidate.

Policy:

- archive historical artifacts before untracking future generated equivalents
- do not delete authority or evidence material without an index
- do not touch Agda source files in generated cleanup

## Ownership Classification

```text
DASHI/                         ours: formal source
Docs/                          ours: docs, roadmaps, authority indexes
scripts/                       ours: helper scripts and data tooling
tests/                         ours: Python test surface
Ontology/                      ours/JMD-adjacent formal lane, do not bulk move
Kernel/ MDL/ Verification/     ours: support formal lanes
.autonomous-orchestrator/      ours: historical orchestration state
.planning/                     ours: planning/inventory state
temp-DOWNLOADED/               historical scratch/downloaded intake
da51_shards/                   tracked DA51 evidence/runtime shards, not submodule
DCHoTT-Agda/                   external submodule
cubical/                       external submodule
Monster-LILA/                  JMD/meta-introspector submodule
monster/                       JMD/meta-introspector submodule
```

## Pass 0 Result

The repo is ready for Pass 1 only after the paired move plan and import map are
accepted as sufficient starting surfaces:

- `.planning/repo-cleanup-move-plan.tsv`
- `.planning/agda-import-map.tsv`

No cleanup action is promoted by this manifest alone.
