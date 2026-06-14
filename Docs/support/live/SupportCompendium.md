# Support Compendium for Papers 1, 3, and 8

Date: `2026-06-14`
Status: shared support sourcebook; not a flagship manuscript

This compendium is the cleaned support layer for the live corpus:

- `Paper 1`: Navier-Stokes analytic manuscript
- `Paper 3`: Yang-Mills analytic manuscript
- `Paper 8`: closure-architecture manuscript

Each section below is a synthesis rather than a raw archive dump. Every section
records its source file and extraction date.

## 1. GR bridge setup

Source file: `Docs/papers/legacy/Paper2GRGeometryDraft.md`  
Extraction date: `2026-06-09`

Paper 2 establishes the Gate 4 support boundary as a bridge problem rather than
as a promoted continuum GR theorem. The useful material for the live corpus is:

- DASHI has a constructed internal pro-object or compatible-family semantics
  for its refinement tower.
- Typed B0.2 and B0.3 bridge targets exist for holonomy, G-structure, and
  Levi-Civita comparison.
- A finite Lorentzian valuation-metric chain through Christoffel, Riemann,
  Ricci, scalar curvature, Einstein tensor, and contracted-Bianchi bookkeeping
  is staged on selected finite surfaces.
- Wald and Friedmann/Temple receipts remain authority boundaries rather than
  internal promotions.

For the live corpus this material serves two purposes only. First, Paper 8 can
cite it as the canonical example of a lane whose finite and authority surfaces
are real but whose continuum promotion remains closed. Second, it provides a
clean scope-control template: local geometric witnesses do not silently imply
continuum sourced Einstein equations.

## 2. Hilbert/Stone operator route

Source file: `Docs/papers/legacy/Paper4PhysicalHilbertSkeleton.md`  
Extraction date: `2026-06-09`

Paper 4 supplies the operator-theoretic support language needed especially by
Paper 3 and secondarily by Paper 8. The durable support points are:

- there is a typed depth-indexed Hilbert carrier route with isometric
  embeddings;
- finite quotient Hilbert staging and finite Stone-bundle witnesses exist;
- finite traversal and strong-continuity receipts are available at bounded
  scope;
- a self-adjoint finite generator surface is recorded;
- GNS quotient and physical Hilbert completion remain open.

The important support lesson is structural: finite Stone or Hilbert witnesses
can justify operator setup, self-adjointness language, and semigroup
comparison, but they do not by themselves promote a physical continuum Hilbert
space. For Paper 3 this means finite gap data still require a separate
continuum-transfer theorem strong enough to control the vacuum-orthogonal
spectrum without spectral pollution; the live draft now names that as the
`H3a`/`H3b` interface. Paper 8 should consume this support only as part of the
closure grammar's proof-boundary discipline.

## 3. DHR reconstruction support

Source file: `Docs/papers/legacy/Paper5DHRSkeleton.md`  
Extraction date: `2026-06-09`

Paper 5 now feeds the corpus as support rather than as an equal-priority live
manuscript. Its stable contribution is:

- a finite prime-lane DHR receipt layer for `p2`, `p3`, and `p5`;
- finite tensor, braiding, hexagon, star, dual, and statistics surfaces;
- a finite fibre-functor route to Hilbert dimensions `1`, `2`, and `3`;
- a conditional authority state for DHR/DR or Tannaka-Krein reconstruction;
- explicit non-promotion of full arbitrary-sector reconstruction and exact
  `G_DHR ~= G_SM`.

Paper 8 should use this material only through the explicit bridge

```text
JvN inner product on V/null
-> C*-algebra completion
-> DHR sectors as Hilbert bimodules.
```

The point is that DHR illustrates what the inner-product and completion grammar
licenses. It is not part of the proof of the core closure statements, and it
does not by itself construct the compact DHR gauge group or prove
`G_DHR ~= G_SM`.

## 4. Yukawa/CKM diagnostics

Source file: `Docs/papers/legacy/Paper6MatterYukawaCKMSkeleton.md`  
Extraction date: `2026-06-09`

Paper 6 remains a diagnostic reservoir. The clean support material is:

- carrier-side Yukawa matrices and symbolic off-diagonal texture entries exist;
- hierarchy-pattern and suppression-language can be stated honestly;
- alpha readbacks and CKM or Cabibbo comparison targets are available as
  diagnostics;
- physical Yukawa, physical CKM, and empirical promotion remain closed.

This material belongs in the support layer because it is useful for scope and
consumer examples, but it does not define any live theorem frontier for Papers
1 or 3. Paper 8 may cite it only in the limited sense that closure consumers
can feed signature, Clifford, Dirac, or matter-facing structures into later
diagnostic interfaces without promoting phenomenology.

## 5. Scope and terminal non-claims

Source file: `Docs/papers/legacy/Paper7TerminalCompositionDraft.md`  
Extraction date: `2026-06-09`

Paper 7 contributes the strongest current source of scope discipline. The
relevant synthesis for the live corpus is:

- terminal composition requires all component lanes and all cross-gate
  compatibility laws to be promoted at theorem scope;
- finite, conditional, and diagnostic receipts must keep their scope labels;
- no lane may be promoted by analogy with another lane;
- the current terminal verdict remains blocked.

The stale "active blocker" rhetoric from the older draft is removed here. What
remains is a reusable governance rule: every live manuscript should distinguish
what it proves, what it imports under citation, and what it deliberately leaves
open.

## 6. Theorem interfaces, adapters, and manifests

Source file: `Docs/support/reference/AgdaValidationTargets.md`  
Extraction date: `2026-06-14`

The paper-facing route to formal support is the validation target manifest, not
an unfiltered scan of historical receipts. Read these surfaces as candidate
proof support: some are internally Agda-receipted/typechecked integration
points, but they remain pending peer review, external authority review, and
external acceptance. They do not claim Clay problem resolution.

The normalized paper-facing theorem interfaces and generated theorem-variable
manifest are:

- `DASHI/Papers/NavierStokes/TheoremInterface.agda`
- `DASHI/Papers/YangMills/TheoremInterface.agda`
- `DASHI/Papers/Unification/TheoremInterface.agda`
- `scripts/generate_paper_proof_manifest.py`
- `Docs/papers/generated/core_papers_theorem_var_manifest.md`
- `Docs/papers/generated/core_papers_theorem_var_manifest.json`
- `Docs/papers/generated/core_papers_theorem_var_manifest.tsv`

For Paper 1, the current theorem-interface surface is the NS wall listed in
`Docs/support/reference/AgdaValidationTargets.md`, ending at:

- `DASHI/Physics/Closure/NSWriteupAndConstantsReadinessBoundary.agda`
- `DASHI/Physics/Closure/NSStandardPDEWriteupAssemblyBoundary.agda`
- `DASHI/Physics/Closure/NSPaperSubmissionPacketBoundary.agda`

The matching manifest route is:

- `scripts/local_clay_harness_manifest.py`
- `outputs/local_clay_harness_manifest.json`
- `outputs/local_clay_harness_manifest_children/ns_paper_submission_packet_smoke.json`
- `outputs/local_clay_harness_manifest_children/ns_standard_pde_writeup_assembly_smoke.json`

For Paper 3, the current theorem-interface surface is the YM wall listed in
`Docs/support/reference/AgdaValidationTargets.md`, especially:

- `DASHI/Physics/Closure/YMBruhatTitsToOSLatticeTransferBoundary.agda`
- `DASHI/Physics/Closure/YMSpectralMarginToContinuumTransferCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityFullTheoremAssemblyBoundary.agda`
- `DASHI/Physics/Closure/YMPaperSubmissionPacketBoundary.agda`
- `DASHI/Physics/Closure/YMExternalAcceptanceBoundary.agda`

The matching manifest route is:

- `scripts/local_clay_harness_manifest.py`
- `outputs/local_clay_harness_manifest.json`
- `outputs/local_clay_harness_manifest_children/ym_paper_submission_packet_smoke.json`
- `outputs/local_clay_harness_manifest_children/ym_final_authority_packaging_smoke.json`

For Paper 8, the current theorem-interface surface is the unification wall
listed in `Docs/support/reference/AgdaValidationTargets.md`, especially:

- `DASHI/Physics/Closure/UnificationU1aHPerLaneCompositeBoundary.agda`
- `DASHI/Physics/Closure/UnificationCrossTermNullityDiscriminantBoundary.agda`
- `DASHI/Physics/Closure/UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationConsumerAuthorityAssemblyBoundary.agda`
- `DASHI/Physics/Closure/UnificationAuthorityReviewPacketBoundary.agda`

The matching manifest route is:

- `scripts/local_clay_harness_manifest.py`
- `outputs/local_clay_harness_manifest.json`
- `outputs/local_clay_harness_manifest_children/unification_authority_review_packet_smoke.json`
- `outputs/local_clay_harness_manifest_children/unification_consumer_authority_assembly_smoke.json`

Adapter surfaces should be cited only for their bounded role. Current
paper-support adapters include:

- `DASHI/DCHoTT/InterpretationAdapter.agda`
- `DASHI/DCHoTT/All.agda`
- `DASHI/Cubical/NavierStokesCandidate.agda`
- `DASHI/Cubical/YangMillsCandidate.agda`
- `DASHI/Physics/Closure/BoundaryParameterAdapterAlgebra.agda`
- `DASHI/Physics/Closure/UnificationJordanVonNeumannAdapterBoundary.agda`
- `DASHI/Physics/Closure/AtomicChemistryRightLimitsAdapter.agda`
- `scripts/sm_higgs_hepdata_receipt_adapter.py`
- `outputs/sm_higgs_hepdata_receipts/sm_higgs_hepdata_receipt_adapter.md`

These adapters connect paper claims to typed boundaries or diagnostic receipts;
they do not promote downstream physics claims or external acceptance.
The Cubical files are currently fail-closed compatibility records because the
receipt modules they would need to import are not yet checked with
`--without-K` / `--cubical-compatible`.

## 7. Source provenance index

| Compendium section | Source file | Extraction date | Role in live corpus |
| --- | --- | --- | --- |
| GR bridge setup | `Docs/papers/legacy/Paper2GRGeometryDraft.md` | `2026-06-09` | Paper 8 support and scope-control model |
| Hilbert/Stone operator route | `Docs/papers/legacy/Paper4PhysicalHilbertSkeleton.md` | `2026-06-09` | Paper 3 operator setup support |
| DHR reconstruction support | `Docs/papers/legacy/Paper5DHRSkeleton.md` | `2026-06-09` | Paper 8 JvN/completion consumer example |
| Yukawa/CKM diagnostics | `Docs/papers/legacy/Paper6MatterYukawaCKMSkeleton.md` | `2026-06-09` | downstream diagnostic support only |
| Scope and terminal non-claims | `Docs/papers/legacy/Paper7TerminalCompositionDraft.md` | `2026-06-09` | shared claim-boundary discipline |
| Theorem interfaces, adapters, and manifests | `Docs/support/reference/AgdaValidationTargets.md`; `Docs/papers/generated/core_papers_theorem_var_manifest.md` | `2026-06-14` | shared paper-facing theorem-support router |
