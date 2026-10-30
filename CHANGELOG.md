# Changelog

This changelog is append-only. Older mentions of `false` are historical wave
records unless the entry explicitly states it is describing the current live
monitor surface.

## 2026-07-19 — Wetsuit seam optimisation boundary

- Added `DASHI.Geometry.WetsuitSeamOptimisationBoundary`, a fail-closed typed
  carrier for body-zone design priors, material/panel budgets,
  manufacturability evidence, weighted seam cost, admissibility, relative
  optimality, validation gates, and split advice.
- Added `DASHI.Geometry.WetsuitSeamOptimisationRegression` with canonical
  underarm/inner-leg preference and shoulder/spine avoidance prior receipts,
  while keeping continuum optimality and manufacturing authority explicitly
  unpromoted.
- Added the compact aggregate `DASHI.Geometry.WetsuitSeamOptimisation`.
- The module formalises the optimisation and obligation surface only; it does
  not claim universal biomechanics, continuum-mechanics closure, or certified
  manufacture. `DASHI.Everything` was not run in this connector-backed pass.

## 2026-07-13 — P06 duplicate-free valid-walk enumeration

- Added and focused-checked `P06GeneratedWalkUniqueness.agda`.  Under the
  canonical neighbour adapter it proves extension-block `NoDuplicates`,
  recursive block disjointness, and
  `generatedWalkVertexListsNoDuplicates` without postulates or proof-heavy
  `WalkObject` equality.
- Added `GeneratedWalkVertexListSemantics`, packaging generated valid-walk
  lists, extensional completeness, duplicate-freedom, and the single
  `countWalks ≡ length` bridge.
- Added focused-checked additive `P06ConcreteEnumerationEndpoint.agda` and
  `P06SkeletonEnumerationSurface.agda`.  The former makes DFS membership an
  explicit field of a membership-indexed map; neither module touches the
  legacy total-index API.
- Added focused-checked `P06ConcreteSkeletonWitness.agda`, which proves all
  individual-candidate chooseN facts and packages the remaining skeleton list
  obligations (`complete`, vertex-list uniqueness, and count agreement)
  without pretending they are derivable from an arbitrary list.
- Added focused-checked `P06DFSValidWalkSurface.agda`.  It packages the
  minimal per-skeleton `WalkObject` plus equality to `dfsWalkRange`, derives
  generated-list membership and soundness, and adapts map witnesses to the
  membership-indexed endpoint.  It deliberately does not infer path validity
  from `DFSCover` coverage alone.
- `Everything.agda` was not run.  The remaining P06 mathematical blocker is
  now the genuine DFS-valid-walk membership witness; the legacy total-index
  record remains compatibility-only.

## 2026-07-13 — Corrected P06 walk status

- Corrected the P06 record: recursive walk completeness has landed through
  `walkObjectsCompleteByVertices`, and successor-membership inversion has
  landed through `walkObjectsSucMemberByVertices` and
  `walkObjectExtendMemberByVertices` in
  `DASHI/Physics/YangMills/GraphCombinatorics.agda`.

## 2026-10-30 — twin-prime CT11-to-M15 exact support bridge (PR #1408)

- Added `DASHI.Arithmetic.TwinPrimeMangoldtProperPowerCandidateCoverageExact`: real support -> computed duplicate-free power image, nonzero residual endpoint inclusion and exact zero-if-outside theorem, using prior owners.
- Constructed the numeric base ≥2 bridge from the original certified Chebyshev Nat-prime carrier; rejected any assumption that abstract `toNat` alone implies primality.
- Imported through `DASHI/EverythingTOESymmetryResolved369.agda`, `DASHI/Unifier.agda` and `DASHI/Unified/Everything.agda`; updated roadmap, paper and TODO; committed a finite overcount/support adversary regression.
- Checked actual Agda/Lean and recent PR sources, not just PR descriptions; original authors and semantic admission gates retained, no ESD modifications.
- **Evidence boundary:** source-written and independent numeric oracle only. Agda/Lean kernel closure, complete ordered scalar, CT13–CT14 error asymptotic and CT15 positivity remain unproved. CI not run.

## 2026-10-30 — CT13 finite error-position image envelope (#1408 continuation)

- Reused the CT11 candidate image and generic Nat-list deduplicator to source-write two-position-per-value coverage, exact envelope length, zero duplicate positions, and a bound `2*floorSquareRoot(U)*floorBinaryExponent(U)` for the numeric covering set.
- Connected certified nonzero retained Mangoldt errors to this set; no candidate image is mistaken for certified primality or a signed-correlation theorem.
- Independent local exact-number test covered 1,998,997 shifted positions across U=4..2000 with zero support misses. Updated the committed regression; exact checkout execution unavailable. Kernel typechecking, ordered real weight bounds and CT15 remain open.

## 2026-10-30 — CT15 frontier parity attempt and observer-sensitive exact M16 route

- Extended original proper-power 25/27 no-go Agda owner with the true prime 103 versus odd squarefree composite 105=3×5×7 counterexample to promotion of negative Möbius signs into true twin pairs, using original certified Nat-primality/factorisation.
- Committed exact finite signed-parity / cube-roughness diagnostic; an independently executed equivalent Python oracle passed five dyadic windows, X=10,000..1,000,000, showing at X=1M: 26,607 negative sign partners = 6,702 twins + 19,905 odd squarefree composites.
- Extended original M16 Mangoldt finite witness module with exact `S!=E` and observed-separation lemmas and a conditional cofinal observer→twin infinitude composition. The missing cofinal separation is NOT asserted or proved.
- Reused existing Core.pow2 and in-repo Data.Nat.Logarithm precedent; added standard library floor-log₂ bound, source equality with custom cutoff, and duplicate-safe stdlib-log rectangle coverage.
- Updated research proof matrix, paper and TODO. No ESD paths touched, no CI. Agda/Lean compilers unavailable, all new Agda theorem source remains kernel pending; no twin-prime infinitude or parity breakthrough is claimed.
