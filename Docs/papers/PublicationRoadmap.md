# DASHI Publication Roadmap

Date: `2026-06-14`
Declared surface level: `publication router`

This roadmap is the canonical planning surface for publication sequencing. It
does not promote any theorem, Clay claim, external authority claim, or peer
review status. It records how the current paper corpus should be prepared from
the repository's proof-first surfaces.

## 21 November 2026 — current paper-corpus review and committed updates

The **original eight numbered paper families** remain tracked here.
The **live three-paper core** is still Paper 3 (YM), Paper 1 (NS),
and Paper 8 (closure/receipt grammar), NOT eight currently
submission-ready mathematical theorems. This review also recognizes
other separately authored or repository-local research manuscripts,
including the atomic/periodic-table draft
`Docs/papers/drafts/DASHIAtomicPeriodicTable369Formalism.tex`
and the separately scoped
`Docs/papers/drafts/YangMillsClayTrackAuditManuscript.tex`.
Those are not automatically promoted to the three-paper core.

**Update ranking for the November proof corpus:**

| Priority | Paper and source owner | Editorial decision and mathematical reason |
| --- | --- | --- |
| **P0 / committed** | **Paper 3** `live/Paper3YangMillsClayDraft.md`; active Agda YM #1536 | Unified duplicate abstracts; replaced old single-`H3a` main theorem emphasis with conditional same-original `F1/F3/F4` source obligations. Added finite F19/R445 original Wilson 1,024=128+896 spectator/wilson-action counterexample and explicit no-physical-gap firewall. The live draft is revised on #1536; do not infer master publication readiness. |
| **P0 / committed** | **Paper 8** `live/Paper8UnificationDraft.md`; active Agda GRH #1533 | Added original Dirichlet GRH five-theorem authority, independently reported source verification, Lean v4.33.1 adapter, Mathlib-to-Clay root, Agda RH-only conditional same-object boundary, and exact primitive/imprimitive Euler-factor donor as a *case study* of four-layer receipt governance. This does not convert Paper 8 into a GRH proof manuscript. |
| **P0 / committed on NS PR #1539** | **Paper 1** `live/Paper1NavierStokesClayDraft.md`; [source-first NS #1539](https://github.com/chboishabba/dashi_agda/pull/1539) | Rewrote the stale A1–A9 opening and R752 universally-positive W2 premise as a conditional compiler, incorporated real physical R734/R735 N=2 and R820/R823/R825 3–4–5 auxiliary signed-payment no-gos, and explicitly left the R751/R752→falsified-rate same-source identity OPEN. Original W1, alternative signed B2 estimate, all-data continuation and A/C/D distinctions remain unproved. Independent SymPy 1.14 exact arithmetic and status-regression PASS; no CI/Agda/Lean kernel. The manuscript and current `NSProofControl20260915.md` roadmap changes are committed on #1539, not master. |
| **P2 / retain as satellites** | **Papers 2,4,5,6** in `legacy/` | GR/DCHoTT, Hilbert/Stone, DHR, and Yukawa/CKM remain limited or diagnostic. Reopen only when new physical, analytic or carrier-level statements are genuinely proved and source-authority checked. |
| **P2 / folded, not separate terminal proof** | **Paper 7** `legacy/Paper7TerminalCompositionDraft.md` | Retain its obligation-map role in Paper 8; no promoted unified-physics theorem. |
| **Separate research drafts** | Atomic/periodic-table TeX, YM audit TeX, selected Monster/TOE studies | Audit attribution and intended venue/claims independently; do not silently renumber as Paper 9/10 or treat them as current active core without a source-based publication decision. |

**Source-first mathematical claim boundary (November):**
- Original 4D YM physical E1 and full nonvacuum D2 gap, required
  continuum/volume uniform estimates, N1 nontriviality and all compact
  simple G remain OPEN. F19/R445/CMP and finite 128+896
  Wilson block-fibre geometry are iterative proof donors only.
- External original all-Dirichlet-character GRH (five published Lean
  statements; externally reported kernel verification) is distinct
  from DASHI-local Lean toolchain-compatible admission and Agda
  per-character analytic identity, both still OPEN. Ordinary zeta RH
  does **not** provide the reverse all-character GRH implication.
- Selected conductor-32 BSD has an original Mellin split and a
  conditional positive eta tail bound; same original E32 analytic
  L-function/newform/eta identification and universal BSD remain OPEN.
- Paper 1 NS W1/W2 or its updated original physical frontier
  requires its own PDE source proofs; cross-domain algebra is no
  substitute.
- Preserve original author, independent verifier and DASHI
  adapter attribution separately. Local SymPy arithmetic and
  source readback are **not** Lean/Agda kernel acceptance. No paper
  claims Clay solution, publication approval or proof-completion
  from a commit count.

**Next editorial implementation:** synchronize each revised
manuscript with its theorem-variable manifest and source
citation ledger, review current YM/NS physical assumptions and
the original GRH pinned source statements, and select any satellite
only after a source-owned theorem/publication purpose is identified.
The old June 2026 priority descriptions below remain historical
publication staging guidance; this dated section governs current
source-critical edits.

---

### 21 November 2026 — Paper 1 source-first update now committed

Focused draft [NS PR #1539](https://github.com/chboishabba/dashi_agda/pull/1539)
is based on `master` and changes the existing live
`Paper1NavierStokesClayDraft.md`, **not** a new ninth paper.
It retains the original A/B/C/D alternatives and R744–R752
conditional mathematical identities, but explicitly distinguishes
the **physically refuted unrestricted** R734/R735 and
R820/R823/R825 positive-payment conjectures from the **unresolved**
literal source-identity question for `G_751`. Original W1,
a new signed replacement B2 inequality and uniform actual-flow
continuation are not proved; the negative auxiliary decision is
not a counterexample to NS regularity.

The **single authoritative current NS roadmap**
`Docs/roadmaps/NSProofControl20260915.md` has been
updated and committed on the *same NS PR #1539*.
Its historical wide NS roadmap also redirects to that owner.
New local SymPy 1.14 regression verifies exact R853/R854
rational rates and R820/823/825 algebra with negative controls;
no Agda/Lean/CI result is inferred.

This source-critical Paper 1 work is independent of the
Paper 3/YM #1536 and Paper 8/GRH #1533 branches. This
**publication roadmap is updated here on #1533** because the
Paper 8 manuscript edit already owns the current
eight-family publication-router update; avoid concurrent
different edits to its master-base version.

---

## Claim Boundary

The publication language for Clay-facing papers is:

```text
candidate proof package, internally DASHI/Agda-receipted where stated,
pending independent peer review, external authority review, and the applicable
Clay Mathematics Institute eligibility procedures.
```

The papers should avoid any language that implies Clay approval, solution
status, or acceptance unless the external review and Clay governance facts have
actually occurred.

## Current Corpus Decision

The old eight-paper plan has collapsed into a three-paper core plus support and
satellite tracks.

The current core is:

1. `Paper 3`: Yang-Mills Clay-facing candidate.
2. `Paper 1`: Navier-Stokes Clay-facing candidate.
3. `Paper 8`: closure grammar / formal architecture companion.

The remaining old paper lanes are not deleted. They are source material,
support examples, or later satellites unless a future router explicitly
promotes them.

## Priority 1: Paper 3, Yang-Mills

Live manuscript:

- `Docs/papers/live/Paper3YangMillsClayDraft.md`

Formal support:

- `DASHI/Papers/YangMills/TheoremInterface.agda`
- `Docs/papers/generated/core_papers_theorem_var_manifest.md`
- `Docs/support/live/SupportCompendium.md`

Reason for first priority:

- the narrative is the cleanest reviewer path: finite self-adjointness,
  domination, spectral margin, continuum transfer, no spectral pollution,
  reflection positivity, OS/Wightman reconstruction, and mass-gap assembly;
- the central scrutiny point is well localized: continuum transfer strong
  enough to preserve the vacuum-orthogonal gap;
- the current paper already has conservative authority-backed, non-promoting
  status language.

Required update before submission:

- make the finite lattice gap versus continuum physical mass gap distinction
  explicit in the introduction and in the transfer section;
- move the Mosco / norm-resolvent / no-spectral-pollution interface into a
  theorem-level statement with exact hypotheses;
- convert the `H3a` Balaban authority socket into an explicit intake chain:
  block-spin RG, Balaban 1988 Lemma 3 / cluster-expansion activity bound,
  polymer summability, Casimir suppression on the vacuum-orthogonal sector,
  trace-norm transfer, and Seiler compatibility;
- keep Option B, the DASHI-native polymer-bound rederivation, separated as a
  companion-paper target rather than as a hidden premise of the current draft;
- cite the generated theorem-variable manifest as a formal supplement, not as a
  substitute for the prose proof;
- keep the abstract, status box, formal-support appendix, and claim-boundary
  table aligned on candidate preprint language;
- keep terminal Clay promotion false until external governance changes.

Submission target state:

```text
independently readable mathematical physics preprint with a formal supplement.
```

## Priority 2: Paper 1, Navier-Stokes

Live manuscript:

- `Docs/papers/live/Paper1NavierStokesClayDraft.md`

Formal support:

- `DASHI/Papers/NavierStokes/TheoremInterface.agda`
- `Docs/papers/generated/core_papers_theorem_var_manifest.md`
- `Docs/support/live/SupportCompendium.md`

Reason for second priority:

- it is mathematically highest-stakes and likely to receive the harshest
  review;
- it must be self-contained as a PDE paper and must not depend on the reader
  accepting the unification architecture first;
- the strongest exposition burden is the A6 defect-from-critical coercivity
  narrative and the exact constant budget feeding A7-A9.

Required update before submission:

- rewrite the A6 section around defect-from-critical coercivity rather than
  negative stretching sign;
- state the Seregin/ESS intake as an `A3.2` compactness theorem only, with
  `delta_r = O(r^(1/12))` recorded as the `A3.3` Abel-weighted target rather
  than a derived theorem;
- add the route-compatibility boundary separating this paper's tail-flux /
  Abel-defect route from the independent Sprint164 microlocal `Sigma` route;
- provide a constant table for the depletion and Gronwall thresholds;
- separate accepted external PDE inputs from internal DASHI receipts and
  diagnostic harnesses;
- keep the formal-support appendix explicit that theorem-interface receipts do
  not promote `A1/A3` or `A4`;
- keep the formal status box conservative: candidate proof package, not Clay
  resolution.

Submission target state:

```text
independently readable PDE preprint with exact lemma dependencies and a formal
supplement.
```

## Priority 3: Paper 8, Closure Grammar

Live manuscript:

- `Docs/papers/live/Paper8UnificationDraft.md`

Formal support:

- `DASHI/Papers/Unification/TheoremInterface.agda`
- `Docs/papers/generated/core_papers_theorem_var_manifest.md`
- `Docs/support/live/SupportCompendium.md`
- `Docs/support/reference/AgdaValidationTargets.md`
- `DASHI/DCHoTT/InterpretationAdapter.agda`
- `DASHI/DCHoTT/All.agda`
- `DASHI/Cubical/NavierStokesCandidate.agda`
- `DASHI/Cubical/YangMillsCandidate.agda`

Reason for third priority:

- it explains the receipt layer, theorem interfaces, fail-closed governance,
  Cubical/DCHoTT adapters, and consumer discipline;
- it is useful after Papers 1 and 3 exist as concrete anchors;
- published too early, it risks looking like a framework paper asking readers
  to trust the architecture before seeing the analytic proof claims.

Required update before submission:

- add the four-layer formal support story: receipt layer, theorem-interface
  layer, Cubical/DCHoTT adapter layer, controlled consumer layer;
- add a generated Paper 8 theorem-variable manifest once its interface is
  stable;
- describe wider lanes only as scoped consumers, examples, or satellites;
- keep terminal unification false unless the live `UCT.1-UCT.4` wall is
  actually promoted.

Submission target state:

```text
methods/architecture preprint explaining how DASHI proof receipts and paper
claim boundaries are governed.
```

## Old Eight-Paper Plan Mapping

| Old paper | Current role | Publication disposition |
| --- | --- | --- |
| Paper 1, NS | core Paper 1 | Clay-facing candidate; prepare now |
| Paper 2, GR bridge | support / later satellite | mine into Paper 8 and possible finite-geometry satellite |
| Paper 3, YM | core Paper 3 | Clay-facing candidate; prepare first |
| Paper 4, Hilbert/Stone | support / later satellite | operator or quantum-methods paper after core |
| Paper 5, DHR | support / later satellite | sector-reconstruction paper after YM context stabilizes |
| Paper 6, Yukawa/CKM | diagnostic support | do not publish as theorem paper yet |
| Paper 7, terminal composition | folded into Paper 8 | claim-boundary and governance material |
| Paper 8, unification | core Paper 8 | submit after Papers 1 and 3 are public drafts |

## Satellite Pipeline

Satellites should not block the core papers.

### Satellite A: Formal Receipt Architecture

Topic:

- DASHI fail-closed receipts, theorem interfaces, generated manifests,
  DCHoTT/Cubical adapters, and proof-first repository governance.

Trigger:

- after Paper 8 has a stable manifest and the core papers cite the formal
  supplement cleanly.

### Satellite B: Quantum / Operator / Avian Compass

Topic:

- finite quantum and operator surfaces, radical-pair or avian compass
  observation-quotient material, species+state quotient completion, bounded
  physical interpretation, and avian magnetoreception treated as perceptual
  quotient geometry rather than qualia geometry.

Trigger:

- after the core Clay-facing preprints are posted, so the project is not
  diluted by publishing consciousness-adjacent or biology-adjacent claims in
  the same first wave.

### Satellite B2: Observer Quotients / Transcript PNF / Phenomenal Non-Recovery

Topic:

- ITIR/SensibLaw-style PNF over qualitative-experience transcripts,
  observer-specific perceptual quotient surfaces, cross-observer projection
  defects, audit-bounded runtime PNF seams, multi-observer quotient fusion,
  avian magnetoreception as the best constrained extra-fibre example, and
  explicit non-recovery of phenomenal content.

Formal support:

- `DASHI/Interop/QualiaTranscriptPNFSemanticBridge.agda`
- `DASHI/Biology/ObserverPerceptualManifoldResidual.agda`
- `DASHI/Biology/AvianMagnetoreceptionExtraFibreBoundary.agda`
- `DASHI/Reasoning/MultiObserverScienceQuotientQualiaBridge.agda`
- `DASHI/Reasoning/ObserverQuotientCompleteStatement.agda`
- `Docs/papers/drafts/Paper8QualiaTranscriptPNFSectionDraft.md`

Trigger:

- after Paper 8 has introduced the closure grammar and after the Clay-facing
  preprints are already public. This lane may be cited as an example of
  fail-closed report-structure handling, but it should not be mixed into the
  first-wave NS/YM submissions.

Publication posture:

- this is the merged home for the former `Qualia / Observation Quotient`
  satellite. It should be framed as observer quotient reconstruction and
  phenomenal non-recovery, not as a consciousness solution.

### Satellite C: GR / Finite Geometry / DCHoTT

Topic:

- finite geometry, depth-closed conditions, DCHoTT interpretation adapters, and
  controlled non-promotion of continuum GR.
- BT/Perelman analogue boundaries: product-tree ball growth and entropy,
  Gaussian reduced-volume convergence as a discrete series, BT neck/JSJ
  analogue placement, and explicit false sockets for smooth Ricci flow,
  Perelman monotonicity, surgery, JSJ uniqueness, and Thurston geometrization.

Formal support:

- `DASHI/Physics/Closure/BTBallVolumeEntropyBoundary.agda`
- `DASHI/Physics/Closure/BTGaussianReducedVolumeBoundary.agda`
- `DASHI/Physics/Closure/BTNeckJSJGeometryAnalogueBoundary.agda`
- `DASHI/Physics/Closure/PerelmanRicciFlowAndGeometrizationBoundaryReceipt.agda`
- `scripts/perelman_bt_geometry_boundary_audit.py`

Trigger:

- after Paper 8, because it uses the closure grammar as its claim boundary.

### Satellite D: DHR / Sector Reconstruction

Topic:

- finite sector receipts, DHR/DR authority boundaries, and consumer behavior
  after quotient and completion.

Trigger:

- after the Yang-Mills paper's formal status stabilizes.

### Satellite E: Reserved / Merged

Topic:

- reserved. The former `Qualia / Observation Quotient` topic is merged into
  Satellite B2 so that transcript PNF, observer residuals, avian extra-fibre
  geometry, and phenomenal non-recovery are governed by one fail-closed paper.

Trigger:

- no independent trigger until a future router splits the merged observer
  quotient paper for a concrete venue reason.

## Integration Rule

The Clay-facing papers do not require preceding papers. They should each be
self-contained:

1. standard construction or setup;
2. exact obstruction or hard interface;
3. new reduction or closure mechanism;
4. explicit claim boundary and formal supplement pointer.

Paper 8 and the satellites may cite the core papers. The core papers should not
ask reviewers to first accept Paper 8.

## Immediate Work Queue

1. Update Paper 3 to submission-standard prose.
2. Update Paper 1 to submission-standard prose.
3. Generate and cite theorem-variable manifests for all core papers.
4. Update Paper 8 after Papers 1 and 3 stabilize.
5. Only then select one satellite, with `Quantum / Operator` preferred over
   `Observer Quotients / Transcript PNF / Phenomenal Non-Recovery`.

## Promotion Gates

Internal promotion requires:

- Agda typecheck of the relevant theorem interface;
- generated manifest freshness;
- exact paper status language;
- no terminal Clay or unification claim strengthened by prose.

External promotion requires:

- independent peer review;
- journal or equivalent external acceptance where relevant;
- the applicable Clay Mathematics Institute waiting and eligibility procedures.
