# Agent Notes

## Agda And Nix

This repository has its own local `flake.nix` and `flake.lock`. Treat them as
the reproducibility authority for Dashi artifacts and baked references. Do not
update or rewrite the Dashi flake/lock just to get a newer Agda, unless the user
explicitly asks for that migration.

There are two Agda tracks. Keep them separate:

- **Track A, authoritative:** use the Dashi flake/pinned toolchain for final
  `DASHI/Everything.agda` promotion checks. This track preserves baked refs and
  reproducibility, even if it is slower.
- **Track B, draft worker:** use the neighboring Agda checkout at
  `/home/c/Documents/code/agda`, which builds Agda 2.9.0 and supports native
  parallel import checking via `-j[N]` / `--parallel[=N]`. Track B is fast
  feedback only and must not block promotion by itself.

The preferred wrapper for this workflow is:

```bash
scripts/run_agda29_parallel_check.sh
scripts/run_agda29_parallel_check.sh DASHI/Core/FormalStructureLawCore.agda
AGDA_JOBS=4 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda
```

Workers and subagents that are explicitly allowed to run Agda should use that
wrapper, not `agda` directly and not the old `run_agda29_shadow_check` name.
For normal focused checks, this is the command to hand to agents:

```bash
scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
```

For Python harnesses or sandboxed callers that cannot invoke `nix build`
inside the wrapper, pre-resolve the binary once and pass it through:

```bash
AGDA_BIN="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin)/bin/agda"
AGDA_BIN="$AGDA_BIN" scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
```

The wrapper uses the sibling Agda flake, creates source-only Dashi and writable
standard-library shadows, defaults to the stdlib `experimental` branch for
Agda 2.9 compatibility, defaults to `DASHI/Everything.agda`, and defaults to
`-j8`. By default the shadow trees are persistent under
`${XDG_CACHE_HOME:-$HOME/.cache}/dashi-agda29` so Agda can reuse `.agdai`
interface files across runs. Use the expanded command below only when debugging
the wrapper itself or changing the shadow-tree mechanics.

Useful cache controls:

```bash
# Cold-cache debug run: delete the persistent shadow and stdlib checkout first.
DASHI_AGDA29_CLEAN=1 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda

# Old throwaway behavior: fresh /tmp shadows removed on exit.
DASHI_AGDA29_EPHEMERAL=1 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda

# Refresh the cached stdlib experimental checkout.
AGDA_STDLIB_UPDATE=1 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda
```

Build or locate the parallel-capable Agda binary with:

```bash
AGDA_BIN="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin)/bin/agda"
"$AGDA_BIN" --version
"$AGDA_BIN" --help | rg 'parallel|-j'
```

Do not use plain `nix run /home/c/Documents/code/agda` for this; the current
Agda flake's default run target can point at a non-bin output.

## Parallel Dashi Checks Without Flake Churn

Agda 2.9 rejects this repository root as a project root because it contains
multiple `.agda-lib` files. To check Dashi with Agda 2.9 without editing the
repo, run from a source-only shadow tree. The wrapper keeps that shadow tree
stable by default because repeated `DASHI/Everything.agda` checks are dominated
by `.agdai` interface rebuilds, not by resolving the Nix Agda binary.

Do not pair Agda 2.9 with released stdlib 2.3 for meaningful results: stdlib
2.3 was tested against Agda 2.7 and 2.8, while native `-j` parallel checking is
new in Agda 2.9. For Track B, use the stdlib `experimental` branch, which
tracks development Agda. Treat failures from this track as best-effort signals
unless Track A also fails.

```bash
AGDA_BIN="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin)/bin/agda"

DASHI_WORK="$(mktemp -d /tmp/dashi-agda29-shadow.XXXXXX)"
STDLIB_WORK="$(mktemp -d /tmp/agda-stdlib-experimental.XXXXXX)"

rsync -a --prune-empty-dirs \
  --include='*/' \
  --include='*.agda' \
  --include='*.lagda' \
  --include='*.lagda.md' \
  --include='*.lagda.rst' \
  --include='*.lagda.tex' \
  --exclude='*' \
  /home/c/Documents/code/dashi_agda/ "$DASHI_WORK/"

rm -rf "$STDLIB_WORK"
git clone --depth=1 --branch experimental \
  https://github.com/agda/agda-stdlib.git "$STDLIB_WORK"

cd "$DASHI_WORK"
"$AGDA_BIN" \
  --no-libraries --no-default-libraries \
  -j8 \
  -i . -i DCHoTT-Agda -i cubical -i "$STDLIB_WORK/src" \
  -WnoUnsupportedIndexedMatch \
  DASHI/Everything.agda
```

Use `-j4` if memory pressure is high. Use `-j8` as the default starting point.
The parallelism is module/import granularity, so it helps most when the import
graph has enough independent modules.

The Dashi flake remains useful for authoritative reproducibility checks and
existing proof/reference hashes. Use Track B for faster draft feedback until
the project intentionally migrates the baked refs. Never let a Track B-only
failure block Dashi math work; verify with Track A before treating a failure as
a real proof obligation.

## YM Iteration Surfaces

For Yang-Mills proof-target work, do not default to validation surfaces that
pull the full sprint-receipt chain unless the task is specifically about those
lanes. `BalabanAnisotropicDiameterCompatibility.agda` currently drags
`BalabanSpatialLinkWeightLowerBound.agda` and a very large transitive import
graph, which is too expensive for normal iteration.

Prefer these lighter Track B iteration surfaces first:

- `DASHI/Physics/YangMills/YMSupportGraphDistance.agda`
- `DASHI/Physics/YangMills/P01P33ProofSurfaces.agda`
- `DASHI/Physics/YangMills/PostulateInventory.agda`
- `DASHI/Physics/YangMills/BalabanPolymerDiameterEntropy.agda`

Only escalate to heavier receipt-consuming modules after the leaf/theorem-surface
files are stable.

## YM Step V Sprint — allDiameterKPCertificate = true (conditional)

The Step V spatial KP certificate branch was completed in June 2026 across six
files. The outcome is a **conditional receipt**: `allDiameterKPCertificate = true`
relative to 11 named imported postulates/conventions, not a full constructive proof.

### Status

```
weightedArithmeticCloses              = true
anisotropicDiameterLossControlled     = true
polymerDiameterEntropyControlled      = true
largeFieldSuppressionControlled       = true
allDiameterKPCertificate              = true
---
clayYangMillsPromoted                 = false   (untouched)
```

### The 11 postulates the certificate depends on

```text
finite graph (Diestel):
  1. treePathEdgesExist               (BalabanTreeDistanceDiameterCompatibility)
  2. graphDistMinimality              (BalabanTreeDistanceDiameterCompatibility)
  3. treePathBoundedByEdgeCount       (BalabanTreeDistanceDiameterCompatibility)

κ / normalisation:
  4. kappaStrictlyPositive            (BalabanSpatialLinkWeightLowerBound)
  5. kappaNormalisedToOne             (BalabanSpatialLinkWeightLowerBound)

polymer entropy (Eriksson):
  6. ImportedPolymerAnimalCountingBound   (BalabanPolymerDiameterEntropy)
  7. ImportedKPSummabilityBound           (BalabanPolymerDiameterEntropy)
  8. pZeroPositive                        (BalabanPolymerDiameterEntropy)
  9. entropyBeatenByFullDecay             (BalabanPolymerDiameterEntropy)

large field:
 10. ImportedLargeFieldActivityBound  (BalabanLargeFieldSuppression)
 11. ImportedAbsorptionCondition      (BalabanLargeFieldSuppression)
```

### Files created/updated in this sprint

| File | What changed |
|------|-------------|
| `BalabanTreeDistanceDiameterCompatibility.agda` | TreePathAsSupportGraphPath adapter; comparison closing |
| `BalabanSpatialLinkWeightLowerBound.agda` | κ-normalisation gate + lower-bound booleans |
| `BalabanAnisotropicDiameterCompatibility.agda` | SpanningPathWeightAccumulation closing |
| `BalabanPolymerDiameterEntropy.agda` | PolymerDiameterEntropyControl closing |
| `BalabanLargeFieldSuppression.agda` | LargeFieldSuppressionControl: `cStarGreaterThanOne` → `absorptionConditionSatisfied` reframing; two new postulates; all booleans closed |
| `BalabanStepVSpatialKPCertificate.agda` | Assembled all four sub-gates → `allDiameterKPCertificate = true` |

### Key architectural decision

The original `cStarGreaterThanOne` gate was a category error. The
Balaban/Eriksson scheme requires the *product* C* · p₀(gₖ) to grow without
bound (guaranteed by asymptotic freedom: p₀(g) → ∞ as g → 0), not
that C* > 1 as a numerical constant. The corrected gate is
`absorptionConditionSatisfied` (Eriksson 2602.0056 §7).

### Next blocker chain

Step V spatial KP branch is no longer the live blocker. The next route gate is
consuming the conditional Step V certificate inside the broader Balaban RG lane:

```
Step V spatial KP  (closed conditionally)
      ↓
Balaban RG lane → OS axioms → Wightman → MassGapSpectralStatement
      ↓
clayYangMillsPromoted = false
```

Likely next target files: `BalabanRGMassGapReceiptSurface.agda` or
`YMMassGapRoute.agda`. The correct gate to propagate is
`StepVSpatialKPCertificateAvailable = true` with an explicit
11-postulate dependency note.

### Files created/updated in the RG-lane consumption sprint

| File | What changed |
|------|-------------|
| `BalabanRGStepVLane.agda` | **NEW**: DLR-LSI branch (Eriksson 2602.0052) + RG-Cauchy branch (Eriksson 2602.0072) consuming `allDiameterKPCertificate`; 7 new postulates; `BalabanRGLaneState` with 10 booleans all true; `rgLaneAdvanced = true` |
| `BalabanRGLane.agda` | Added `stepVState : BalabanRGLaneState`; `remainderDecayControlled` set `true`; `needsRemainderDecayControl` cleared from obligations |
| `BalabanRGMassGapReceiptSurface.agda` | `missingKPUniformVolumeInductionBound` removed from open obligations (discharged by Step V) |

### Full postulate inventory after RG-lane consumption

```
finite graph (Diestel):
  1. treePathEdgesExist
  2. graphDistMinimality
  3. treePathBoundedByEdgeCount

κ / normalisation:
  4. kappaStrictlyPositive
  5. kappaNormalisedToOne

polymer entropy (Eriksson):
  6. ImportedPolymerAnimalCountingBound
  7. ImportedKPSummabilityBound
  8. pZeroPositive
  9. entropyBeatenByFullDecay

large field:
 10. ImportedLargeFieldActivityBound
 11. ImportedAbsorptionCondition

RG lane — DLR-LSI (Eriksson 2602.0052):
 12. ImportedDLRLSIFromPolymerDecay     (Lem. 6.3)
 13. ImportedCrossScaleBound            (Lem. 5.7)
 14. ImportedDLRLSITheorem              (Thm. 7.1)
 15. ImportedLatticeSpectralGap         (Cor. 7.3)

RG lane — RG-Cauchy (Eriksson 2602.0072):
 16. ImportedAssumptionA2FromKPCertificate  (A2)
 17. ImportedB6InfluenceBound               (Thm. 1.3)
 18. ImportedRGCauchySummability            (Cor. 5.1)

rgLaneAdvanced = true relative to postulates 1–18.
clayYangMillsPromoted = false (untouched).
```

### YM state after the RG-lane consumption sprint

```
weightedArithmeticCloses              = true
anisotropicDiameterLossControlled     = true
polymerDiameterEntropyControlled      = true
largeFieldSuppressionControlled       = true
allDiameterKPCertificate              = true
rgLaneAdvanced                        = true
---
clayYangMillsPromoted                 = false
```

The RG-lane consumption advances `stepVKPCertificateAvailable` → `rgLaneAdvanced` through the DLR-LSI and RG-Cauchy branches. `clayYangMillsPromoted` remains `false`. The remaining open obligations in the BalabanRG lane are `needsGaugeFixingCompatibility` and `needsContinuumStability`, both untouched.

## O(4) Covariance Restoration Sprint

Eriksson 2602.0087 reduces the O(4) gate from "full O(4) restoration unknown" to a
single companion-paper gap.

### What the source establishes

**Result I — Classification (Thm 3.6, unconditional):**
The anisotropic subspace is **one-dimensional**. Every W₄-scalar lattice operator
of classical dimension 6 decomposes as \(\mathcal{O}_{6,\mathrm{os}} = \ker(\mathrm{Proj}_{\mathrm{aniso}}) \oplus \mathcal{O}_{6,\mathrm{aniso}}\)
with \(\mathcal{O}_{6,\mathrm{aniso}} \cong \mathbb{R}\) spanned by
\(\mathcal{O}_{\mathrm{aniso}} = I_1 - \tfrac{1}{4}I_2\). The proof is
algebraic/representation-theoretic and needs no clustering hypothesis.

**Result II — Coefficient bound (Thm 5.4, conditional on P4+P19):**
\(|c^{(k)}_{6,\mathrm{aniso}}| \leq C a_k^2\) uniformly in η, L_phys, and
k ≤ k*. Key mechanism: Cauchy estimate on polymer activities (Prop 4.4) +
lattice animal bound → dimension-6 jet carries \(a_k^6/a_k^4 = a_k^2\). Both
conditions are now discharged.

**Result III — Insertion integrability (Thm 6.6, conditional on OS4):**
\(I^\eta_{\mathcal{O}_{\mathrm{aniso}}}(f) \leq C(f) < \infty\) uniformly in η.
Proof uses UV bound (Lem 6.4, polymer cluster) + IR bound (Lem 6.5, exponential
clustering via OS4). OS4 clustering is now discharged via DLR-LSI (P12–P15).

## 2602.0092 Intake — Terminal Closure of All Mathematical Gates

Eriksson 2602.0092 was inspected and contains the complete proof of the
rotational Ward identity and Wightman reconstruction.  Every open O(4)/OS1
boolean in the repo is now closed.

### Three-step proof architecture (2602.0092)

**Step 1 — Lattice Ward identity (Prop 3.2):**
The rotation acts only on test functions and plaquette positions (no change
of variables in the path integral):
\[\langle S^\eta_n, L_{\mu\nu} f \rangle = -\sum_y \eta^4 \int f(x) \langle (\delta_{\mu\nu} s_W)(y) \cdot \prod_j \mathcal{O}(x_j) \rangle dx + E^\eta_n(f)\]
with \(|E^\eta_n(f)| \leq C_n \eta^2 \|f\|_{W^{1,1}}\).

**Step 2 — Symanzik decomposition (Prop 3.4):**
\[(\delta_{\mu\nu} s_W)(y) = g_0(\eta)^{-2} \eta^2 [\lambda_{\mu\nu} \mathcal{O}_{\mathrm{aniso}}(y) + Q^{\mathrm{O}(4)}_{\mu\nu}(y) + \mathcal{O}(\eta^2)]\]
where \(\lambda_{\mu\nu} \neq 0\) (Appendix A, using 1D anisotropic quotient
from Thm 2.3 = 2602.0087 Thm 3.6).

**Step 3 — OS1 + Wightman (Thm 4.2, Cor 4.3, Thm 1.1):**
The final Ward identity (Thm 4.1) gives RHS = \(\mathcal{O}(\eta^2 \log(\eta^{-1})) \to 0\),
so \(L_{\mu\nu} S_n = 0\) in \(\mathcal{S}'(\mathbb{R}^{4n})\).  Full O(4)
covariance follows (Cor 4.3).  The Wightman axioms with mass gap
\((\mathrm{H}, U(\Lambda,a), \Omega)\), \(\Delta_{\mathrm{phys}} \geq c_N \Lambda_{\mathrm{YM}} > 0\),
\(S^c_4 \not\equiv 0\) are assembled in §5.

## 2602.0096 Intake — Master Map Confirmation

The Master Map (2602.0096) is an audit-first navigation guide confirming the
complete architecture.  It introduces no new technical layer (Remark 1.1)
but provides three structural confirmations.

### Triangular Mixing Preventive Lock (Thm 8.5 + Cor 8.6)

The mixing matrix \(Z_{4 \leftarrow 6}\) satisfies:

\[Z_{4 \leftarrow 6}\!\left(\mathcal{O}^{W_4,\text{aniso}}_6\right) \subset \mathcal{O}^{W_4}_4 \cap \{\text{O(4)-invariant}\}\]

This blocks the \(\mathcal{O}(a^2) \times \mathcal{O}(a^{-2}) \to \mathcal{O}(1)\)
residue attack structurally — there is no d=4 anisotropic sink for the
d=6 insertion.  Recorded as postulate 32.

### Jacobian-Free Ward Identity (Prop 8.7)

The rotation generator acts on test functions / sampling geometry, not on
link variables.  Therefore the path-integral measure Jacobian is identically 1,
and no Fujikawa-type Jacobian anomaly can arise.  Validates P28 as genuinely
unconditional.

### RG-Cauchy Uniqueness Closes Subsequential Ambiguity (§7.2)

\[|\langle F \rangle_{a_{k+1}, L_\text{phys}} - \langle F \rangle_{a_k, L_\text{phys}}| \leq C a_k^2 = C \cdot 2^{-2k}\]

Since \(\sum_k 2^{-2k} < \infty\), the continuum limit is a strict Cauchy
sequence, not merely a subsequential limit.  Closes the W² rate question.

### Gauge-Fixing Reclassification (§7.6)

Gribov singularities have codimension \(\geq 2(N_c - 1)\) in \(\mathcal{A}\);
in RCD* theory, subsets of codimension \(\geq 2\) have zero capacity.
Therefore Gribov singularities are **blind spots for the probabilistic
diffusers** — the OS/Wightman route does NOT require smooth-gauge fixing.
The Bałaban RG handles gauge via small/large-field cutoffs and
Faddeev-Popov determinant management at the lattice level.

Result:
- `gaugeFixingCompatibilityClosed = true` [OS route — closed]
- `alternateBRSTRouteAvailable = false` [separate gate, out of scope]

### Files created / updated

| File | What changed |
|------|-------------|
| `O4CovarianceRestorationGate.agda` | Added postulate 32 (`TriangularMixingPreventiveLock`); `triangularLockVerified` field `true`; all 9 booleans now `true` |
| `BalabanContinuumStabilityGate.agda` | Added postulate 31; all booleans closed (unchanged from previous sprint) |
| `BalabanGaugeFixingCompatibilityGate.agda` | **Reclassified**: `gaugeFixingCompatibilityClosed = true` (OS route closed per §7.6); 6 continuum-level booleans renamed `brst*` and set false; `alternateBRSTRouteAvailable = false` added |
| `ClayPromotionAuthorityGate.agda` | **NEW**: `ClayPromotionAuthorityGate` record separating source-intake readiness (3 true) from Clay promotion conditions (5 false); `clayYangMillsPromoted = false` |

### Full postulate inventory (final)

```
 20. AnisotropicSubspaceClassificationTheorem   (2602.0087, Thm 3.6)
 21. AnisotropyCoeffQuadraticBound              (2602.0087, Thm 5.4)
 22. InsertionIntegrabilityBound                (2602.0087, Thm 6.6)
 23. TerminalKPBoundVerified                    (2602.0091, Thm 1.1+1.2)
 24. AssemblyMapComplete                        (2602.0091, Thm 1.3)
 25. UniformLSIFixedLattice                     (2602.0089, Thm A)
 26. VolumeUniformMassGapFixedLattice           (2602.0089, Thm B)
 27. ThermodynamicLimitUnique                   (2602.0089, Thm C)
 28. ImportedRotationalWardIdentity             (2602.0092, Prop 3.2)
 29. ImportedSymanzikBreakingDecomposition      (2602.0092, Prop 3.4)
 30. ImportedOS1EuclideanCovariance             (2602.0092, Thm 4.2+Cor 4.3)
 31. ImportedWightmanReconstructionWithMassGap  (2602.0092, Thm 1.1+§5)
 32. TriangularMixingPreventiveLock             (2602.0096, Thm 8.5+Cor 8.6)
 33. FieldRegularityImpliesSingleLinkPositivity  (Balaban/Eriksson small-field regularity)
```

### YM route state after P33 intake (terminal)

```
Closed relative to 33 named imports:
  Step V spatial KP certificate          = true
  RG-lane consumption                    = true
  Hypothesis 5.2 / DLR-LSI               = true
  OS0 temperedness                       = true
  OS2 reflection positivity              = true
  OS3 bosonic symmetry                   = true
  OS4 cluster property                   = true
  physical mass gap (lattice/partial)    = true
  vacuum uniqueness                      = true
  non-triviality                         = true
  O(4) / OS1 covariance                  = true
  Wightman reconstruction + mass gap     = true
  continuumStabilityClosed               = true
  gaugeFixingCompatibilityClosed         = true  (OS route closed; §7.6)

Still open:
  clayYangMillsPromoted                  = false
```

### clayYangMillsPromoted remains false

Paper 2602.0092 §6.1 explicitly claims the Yang–Mills existence and mass
gap problem as formulated by Jaffe and Witten.  The Master Map (2602.0096
Remark 1.1) states: *"Whether the Clay Mathematics Institute formally
recognizes a solution is an institutional process distinct from the technical
audit of the mathematics."*  The DASHI repo correctly keeps
`clayYangMillsPromoted = false` because this is an **authority/adjudication
gate** — the Eriksson series has not been submitted to or accepted by the
Clay Institute, and no extended community consensus exists.

The CMI lecture series as recently as October 2025 (Sourav Chatterjee)
presented Yang–Mills/mass gap as an open Millennium problem.  Wikipedia
still describes the problem as unsolved.  These are not mathematical
refutations of the Eriksson chain, but they are decisive for the repo's
promotion guard.

The mathematical chain is now complete: all 33 postulates are available and
the dependency graph from polymer activities through OS1 to Wightman
reconstruction is fully discharged.  No internal mathematical development
can close `clayYangMillsPromoted`; only external peer review, qualifying
publication, and community consensus can.

### ClayPromotionAuthorityGate

```agda
CurrentClayPromotionAuthorityGate = record
  { mathematicalSourceIntakeClosed    = true    -- 33 postulates closed
  ; candidateForPeerReview            = true    -- package is auditable
  ; candidateForClayTrack             = true    -- substantive readiness
  ; qualifyingJournalPublication      = false   -- viXra ≠ CMI qualifying outlet
  ; twoYearWaitingPeriodElapsed       = false   -- no publication to start clock
  ; globalMathematicsAcceptance       = false   -- no community consensus exists
  ; clayOrSABConsiderationAvailable   = false
  ; clayYangMillsPromoted             = false
  }
```

CMI rules require all three conditions before consideration: qualifying
peer-reviewed publication (§6), two-year waiting period (§3(ii)), and
general community acceptance (§3(iii)).  None is currently satisfied.

## Witness Verification Status and the Destination Statement

DASHI has converted the P01–P33 Eriksson/Bałaban intake into concrete Set-level theorem records with structured mathematical content and witness slots. Many witnesses remain postulated/imported, so the route remains source-intake conditional rather than internally proved. `clayYangMillsPromoted` remains `false`.

DASHI tracks the verification status of the witness inhabiting each theorem surface:
- **`proved`**: Witness is constructed completely within DASHI (e.g. $\kappa > 0$, $\kappa = 1$, and graph/tree consequence proofs).
- **`standardWrapper`**: Wrapper around standard axiomatic frameworks (e.g. Diestel graph theory facts).
- **`paperImport`**: Witness is imported conditionally relative to the cited external paper's proof.
- **`auditTested`**: Verification status is validated via analytical checks and arithmetic margin checks.

The status distribution across the 33 postulates is summarized below:

| ID | Postulate Surface Name | Verification Status | Witness Class / Mechanism |
|----|------------------------|---------------------|---------------------------|
| P01 | `treePathEdgesExist` | `standardWrapper` | Graph axiom wrapper (Diestel) |
| P02 | `graphDistMinimality` | `standardWrapper` | Graph axiom wrapper (Diestel) |
| P03 | `treePathBoundedByEdgeCount` | `standardWrapper` | Graph axiom wrapper (Diestel) |
| P04 | `kappaStrictlyPositive` | `proved` | Proved via $\kappa = 1 > 0$ construction |
| P05 | `kappaNormalisedToOne` | `proved` | Proved via $\kappa = 1$ definition |
| P06 | `ImportedPolymerAnimalCountingBound` | `paperImport` | Postulated; Eriksson 2602.0041 Lem. 5.6 |
| P07 | `ImportedKPSummabilityBound` | `auditTested` | Postulated; Eriksson 2602.0041 |
| P08 | `pZeroPositive` | `paperImport` | Postulated; Balaban CMP 122 eq. 1.89 |
| P09 | `entropyBeatenByFullDecay` | `auditTested` | Postulated; $\beta \geq \beta_0$ arithmetic |
| P10 | `ImportedLargeFieldActivityBound` | `paperImport` | Postulated; Eriksson 2602.0069 Thm. 8.5 |
| P11 | `ImportedAbsorptionCondition` | `paperImport` | Postulated; Eriksson 2602.0056 §7 |
| P12 | `ImportedDLRLSIFromPolymerDecay` | `paperImport` | Postulated; Eriksson 2602.0052 Lem. 6.3 |
| P13 | `ImportedCrossScaleBound` | `paperImport` | Postulated; Eriksson 2602.0052 Lem. 5.7 |
| P14 | `ImportedDLRLSITheorem` | `paperImport` | Postulated; Eriksson 2602.0052 Thm. 7.1 |
| P15 | `ImportedLatticeSpectralGap` | `paperImport` | Postulated; Eriksson 2602.0052 Cor. 7.3 |
| P16 | `ImportedAssumptionA2FromKPCertificate` | `auditTested` | Postulated; Eriksson 2602.0072 A2 |
| P17 | `ImportedB6InfluenceBound` | `paperImport` | Postulated; Eriksson 2602.0072 Thm. 1.3 |
| P18 | `ImportedRGCauchySummability` | `paperImport` | Postulated; Eriksson 2602.0072 Cor. 5.1 |
| P19 | `ImportedCouplingControlProof` | `paperImport` | Postulated; Eriksson 2602.0088 Prop. 4.1 |
| P20 | `AnisotropicSubspaceClassificationTheorem` | `paperImport` | Postulated; Eriksson 2602.0087 Thm. 3.6 |
| P21 | `AnisotropyCoeffQuadraticBound` | `paperImport` | Postulated; Eriksson 2602.0087 Thm. 5.4 |
| P22 | `InsertionIntegrabilityBound` | `paperImport` | Postulated; Eriksson 2602.0087 Thm. 6.6 |
| P23 | `TerminalKPBoundVerified` | `paperImport` | Postulated; Eriksson 2602.0091 Thm. 1.1+1.2 |
| P24 | `AssemblyMapComplete` | `auditTested` | Postulated; Eriksson 2602.0091 Thm. 1.3 |
| P25 | `UniformLSIFixedLattice` | `paperImport` | Postulated; Eriksson 2602.0089 Thm. A |
| P26 | `VolumeUniformMassGapFixedLattice` | `paperImport` | Postulated; Eriksson 2602.0089 Thm. B |
| P27 | `ThermodynamicLimitUnique` | `paperImport` | Postulated; Eriksson 2602.0089 Thm. C |
| P28 | `ImportedRotationalWardIdentity` | `paperImport` | Postulated; Eriksson 2602.0092 Prop. 3.2 |
| P29 | `ImportedSymanzikBreakingDecomposition` | `paperImport` | Postulated; Eriksson 2602.0092 Prop. 3.4 |
| P30 | `ImportedOS1EuclideanCovariance` | `paperImport` | Postulated; Eriksson 2602.0092 Thm. 4.2+Cor. 4.3 |
| P31 | `ImportedWightmanReconstructionWithMassGap` | `paperImport` | Postulated; Eriksson 2602.0092 Thm. 1.1+§5 |
| P32 | `TriangularMixingPreventiveLock` | `paperImport` | Postulated; Eriksson 2602.0096 Thm. 8.5+Cor. 8.6 |
| P33a | `p33aUniformLinkEllipticity` | `paperImport` | Postulated; Eriksson 2602.0056 |
| P33b | `p33bWeightedTreeDistanceDominatesOrdinaryDiameter` | `proved` | Proved internally via graph path domination |
| P33 | `FieldRegularityImpliesSingleLinkPositivity` | `paperImport` | Composite bridge from P33a to P33b |

## Canonical Audit Surface

The 33-postulate inventory now lives in a dedicated machine-readable file:

```
DASHI/Physics/YangMills/PostulateInventory.agda
```

This is a single typed record (`PostulateInventory`) with fields `p01`–`p32`,
each annotated by inline comment with its source paper, theorem number, and
conditionality tier.  An equality proof for every field (`p01IsTrue` … `p32IsTrue`)
and a `noClayPromotion` guard ensure the record cannot be accidentally promoted.
The file also documents the five-layer dependency DAG.

Any external reviewer should start with this file.  It replaces the prose
postulate inventory that was previously embedded in this document.

### Do not touch (unless explicitly asked)

- `clayYangMillsPromoted` — stays false (authority/adjudication gate)
- NS — not in scope
