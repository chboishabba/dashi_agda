> **25 OCT 2026 — LATEST BACKEND-FREE CUT:** Beyond the earlier C2/C3/parity screens, PR #1250 now contains a pure-Python **FULL-CLASS 6.Suz Sym²12/dual character verifier** with independent source class-size and group-order weighted irreducible orthogonality checks, exact `Q(zeta3)` coordinates, complete second-power map, and explicit first-class mismatch witness. An optional source GAP exporter uses the documented `CoeffsCyc(x,3)` extraction without approximation. Local finite-group C2×C3 positive/negative tests **passed**, including eight malformed-source controls. **An actual 6.Suz table export, selected Monster 78 matching receipt and Agda kernel check have NOT been observed.** This does not supersede the original main/MN3B/Monster source-selected quotient matcher; it independently audits its character-level `Sym²` claim. See [portable character audit / proof ledger](./Monster3B6SuzPortableCharacterAudit20261025.md), and keep `IbrahimMonster3B*` source/quotient ownership, Barraclough–Wilson (2007) and Nebe (2025) original attribution intact.

> **25 OCTOBER 2026 — PRIMARY-SOURCE MAX-CUT CORRECTION (latest):** Barraclough–Wilson §5.1 permits *any* irreducible \(6.\mathrm{Suz}\) character as the inflated 729 tensor factor. Earlier faithful-78 **preselection** in the repository main-quotient GAP script was a local filter, NOT the Monster's proven selection. PR #1250 now scans **all** degree-78 outer families and requires the original full main-table split, exact MN3B descent, and positive occurrence in the restricted Monster character to select exactly one. The source-selected family's faithfulness and central C2 trace (either -90 or +66 for the 90-sector) are **OUTPUTS**, not preconditions. Nebe's Sym²78 and faithful78 remain different 6.Suz representations when their central C2 actions differ. Any earlier claim that the Monster *already selects* faithful78 is superseded. See [actual 6.Suz source-family ledger](./Monster3B6SuzExistingSourceFamilyMaxCut20261025.md). The matcher and its revised validator are source-written; no GAP/Agda execution receipt is available in this turn.\n\n# Source-audit max-cut: 6.Suz is already in DASHI / PRs

**Date:** 2026-10-25. **Primary target:** the actual selected Monster 3B 12+78
multiplicity representation, not another free 90-dimensional D4 model.

## 1. Existing owners inspected (not reconstructed)

**Merged/main:**
- `scripts/monster_3b_suzuki_multiplicity_characters.g`: actual CTblLib character table `6.Suz`, `6.Suz.2`, two **faithful 12ab** and two **faithful 78ab** labels, central C3 phases, outer fusion.
- `scripts/monster_3b_suzuki_main_quotient_match.g`: six -> outer fusion; main `3^1+12:6.Suz.2` -> `MN3B` quotient; full class-function main-table products with fused 1458; unique degree17496 and 113724 constituents that descend and occur with positive multiplicity in restricted Monster 196883. Separates extraspecial centre from diagonal kernel (original historical class20) and does NOT identify absolute individual zeta orientation.
- `DASHI/Wikimedia/IbrahimMonster3BSuzukiMainQuotientSameObjectSnowballExact.agda`, `IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact.agda`, `IbrahimMonster3BSuzukiQuotientDescentCorrectionExact.agda`, `IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact.agda` and `IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact.agda`: source-typed mathematical stages and boundaries.
- `scripts/render_monster_3b_suzuki_main_quotient_match.py`, `scripts/check_monster_3b_suzuki_main_quotient_match.sh`: strict receipt renderer/checker. The presence of code does NOT imply GAP ran.

**Open [PR #1098](https://github.com/chboishabba/dashi_agda/pull/1098):** extensive source-written `Monster3BSuzukiProofRelevantOccurrenceHardeningExact.agda`, `Monster3BActualLinearIsotypicTerminalCompilerExact.agda`, `Monster3BNormalizerHomActionLeanReceiptExact.agda`, symplectic-12/Heisenberg lift and Weyl-cocycle/Schur/Hom sources. Critically, the occurrence wrapper explains that **legacy field values of type Set are propositions, not proof inhabitants**. Companion Lean #47 includes a canonical induced action on Hom_E; that remains conditional on actual same-object lifts. No need to rederive these tools.

**Open [PR #1148](https://github.com/chboishabba/dashi_agda/pull/1148):** the independently valid finite geometric nine-cell/JFine D4 action, now separated from any actual Monster D4 embedding by the PR #1250 character obstruction.

## 2. Source-dependent discovery: two genuinely distinct degree-78 families

**Original source provenance**
- R. W. Barraclough, R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, LMS J. Comput. Math. 10 (2007), DOI 10.1112/S1461157000001352.
- Gabriele Nebe, *Symmetrizations of quadratic and Hermitian forms*, J. Algebraic Combin. 61 (2025) article 29, DOI 10.1007/s10801-025-01399-2, §6. Her irreducible degree-78 symmetric-square representation of a faithful degree12 descends to `3.Suz`. The partition (2) character is labelled `χ_80` in that paper, not assigned by this repository.
- CTblLib/ATLAS labels are authoritative character identifiers in the executable pipeline, not direct evidence of a Monster basis intertwiner.

The original Monster quotient matcher expressly filters **faithful degree78** characters of `6.Suz`. Nebe's `Sym²(faithful 12)` is nonfaithful to `6.Suz`, because the central involution acts as `(-I)^2=+I` and is in the kernel. These C2 central characters cannot be identified as full `6.Suz` representations.

| Character source family on 90-space | χ(C2 centre) | χ(C3 centre), for equal nontrivial phases |
| --- | ---: | --- |
| faithful 12 ⊕ faithful 78 | **-90** | 90ζ or 90ζ² |
| faithful 12 ⊕ dual Sym²(faithful12) | **+66** | 90ζ or 90ζ² |

The central trace DIFFERENCE is `156=2×78`. Thus the earlier pure `90ζ` fingerprint and norm8100 **do not** prove equality of the selected Suzuki character. The C2 test refutes that identification **IF the original matcher succeeds in sourcing the selected faithful78 family**. An unexecuted GAP script is not evidence that it has succeeded.

For complete coverage: mixed central C3 values `-78-66ζ`, `-12+66ζ` have norm5292; pure central values `90ζ`, `90ζ²` have norm8100. That is the earlier correct conditional phase/norm calculation, but neither norm distinguishes faithful78 from nonfaithful dual-Sym² when the C3 phase matches.

## 3. Repository implementation and tests

- The ORIGINAL `scripts/monster_3b_suzuki_main_quotient_match.g` retains its same-object producer. It now verifies the 6.Suz **central order-two** character values of its selected faithful degree12/degree78 families, and emits `source_selected_S90_central_C2_trace=-90`, `sym2_candidate_S90_central_C2_trace=66`, and explicit selected-faithful/Sym² nonidentity. These fields only exist in a runtime receipt **if GAP executes successfully**.
- Its `render_monster_3b_suzuki_main_quotient_match.py` and `check_monster_3b_suzuki_main_quotient_match.sh` now reject missing or inconsistent source-C2 fields.
- The lower-level character inventory no longer erroneously demands only two degree78 characters **total**. It keeps the two faithful `78ab` for the original Monster matcher and inventories all nonfaithful degree78 separately, disjointly; the certificate renderer and shell checker verify the inventory partition. The nonfaithful table scan is not a replacement for the original matcher.
- `scripts/monster_3b_suzuki_sym2_character_screen.g` remains a separate full-character/central-kernel comparison of *all* degree78 candidates, including Nebe's family; no assumption of faithfulness is made there.
- `scripts/monster_3b_suzuki_selected78_c2_discriminator.py` performs exact, backend-free C2/C3/C6 calculations and, optionally, consumes a SOURCE-GAP receipt through the existing canonical strict validator. It cannot authenticate whether a claimed external GAP run occurred.
- `DASHI/Moonshine/Monster3BSuzukiSelectedFaithful78C2Exact.agda` and its import in `Monster3BActualKernelCharacterRound4Validation.agda` encode the disjoint signed C2 fingerprints and keep full Monster occurrence as a separate premise. **Source-written; no Agda kernel receipt.**

**Locally executed independent Python receipt:** `/mnt/data/suzuki_6suz/selected_78_c2_audit_receipt.json`, 8 exact central phase/family cases, central C2 values -90 versus 66, central C3 and C6 checks. This is NOT an actual 6.Suz/GAP character-table run.

## 4. Precise next alpha / stop rule

1. **First:** execute existing CTblLib `6.Suz` inventory and *original source-faithful* main-to-MN3B-to-Monster quotient matcher; obtain generated complete ATLAS-labelled source receipts (or identify a concrete mismatch/error). Do not infer success from source-written Agda records.
2. **Second:** run full `Sym²/dual` character-table comparison and pair each nonfaithful degree78 candidate with the faithful source-selected degree78. The central-C2 incompatibility already gives a rigorous *negative* to literal faithful78=Sym²12; a surviving alternative needs a **different** nonfaithful Monster occurrence or a different interpretation of the 12/78 decomposition.
3. **Third:** use existing PR #1098 normalizer-Hom, projective cocycle and same-object lift compilers, **not** a newly postulated 90-space, to identify the selected linear multiplicity and its full normalizer character. Actual Monster coordinate T remains optional for abstract character comparisons but necessary to deliver a specifically requested explicit basis intertwiner.
4. **DO NOT** revive Heisenberg, (D_4), Fourier, C3 zeta, Sym² existence, or group-algebra theorem development as new owners: already completed in other repository surfaces.
5. **No physics promotion:** a finite character identity or signed central trace does not construct a laboratory mechanism, spacetime dynamics or quantum observation principle.

## Proof-status ledger

- **Already owned mathematical/source fact:** 6.Suz and the degree-729 inertia construction, character identities, group quotient and centre, Nebe Sym²78.
- **Exact locally checked:** eight simple C2/C3/C6 central character cases and the -90 vs 66 obstruction arithmetic.
- **Source-written but unexecuted here:** CTblLib runtime, generated source receipts, new Agda central-sign theorem, actual selected Monster normalizer Hom action.
- **Open:** original matched source receipt, actual selected 78 identification and central phase orientation, actual full normalizer action/cocycle and concrete intertwiner.


## 25 October decisive implementation supplement: source-controlled 78 selection

**Evidence hierarchy:** Original Barraclough–Wilson §5.1 allows `eta-hat in Irr(6.Suz)` without a faithfulness restriction. The original authors' separately preserved character-table/quotient data are published at https://www.rwb.me.uk/table/index.html, including `N3BetcTables.tar.gz`; treat the archived table as SOURCE rather than assuming our local helper's 78 filter describes their construction. The in-repo GAP/CTblLib path has NOT yet been executed in this environment.

**Source-driven matcher algorithm** now committed directly in the pre-existing `scripts/monster_3b_suzuki_main_quotient_match.g`:

1. Retain the original source-faithful degree12 pair (its occurrence remains independently checked).
2. Enumerate all `Irr(6.Suz.2)` of degree156 and restrict their full class functions to `6.Suz`. Accept candidate pairs only when they consist of two distinct degree78 irreducibles, each with multiplicity one. No source-faithfulness/central-C3 prefilter is made for degree78.
3. Tensor each qualifying outer pair with the exact published 1458 main-table Heisenberg character. Demand exactly two degree113724 irreducibles, each multiplicity one, then exactly one full-character quotient descent to `MN3B`.
4. Restrict the actual Monster degree196883 ordinary character to `MN3B`; require the descended degree113724 candidate to occur positively. **If zero or multiple degree78 families survive, report error/ambiguous, not a fabricated unique selection.**
5. Only after that derive the 78 family's faithfulness and its central-C2 scalar. The selected degree90 trace is either `-90` (C2 acts -1 on 78) or `+66` (C2 acts +1); the exact C2 equality to Nebe Sym² is a NECESSARY check, not a full Suzuki character isomorphism.
6. Preserve distinct original extra-special central and diagonal-q-kernel coordinates; keep individual ζ versus ζ² orientation explicitly unpaid.

**Receipts and fail-closed schemas:** `render_monster_3b_suzuki_main_quotient_match.py` and its shell regression now validate whichever selected C2 result the original full character calculation produces; they do not hardcode faithfulness. The lower-level candidate inventor `monster_3b_suzuki_multiplicity_characters.g` enumerates ALL degree78 irreducibles with variable count and records faithful and nonfaithful subsets, including C3-trivial classes; its renderer and checker consume the complete inventory without assuming exactly two 78s TOTAL. The original conditional central-C2 no-go Agda module is now named semantically as a **hypothetical faithful-family** statement rather than an actual Monster source-selection finding.

**Observed local evidence:** Synthetic full-selection acceptance tests (both faithful/nonfaithful survivors, five fail-closed negative controls) pass. The earlier eight central C2/C3/C6 cyclotomic families pass. These are local finite tests only, not an authentic GAP/CTblLib source receipt, Agda proof check, or actual Monster intertwiner.

**Updated Pareto:** Source table availability and published generic 6.Suz machinery are NO LONGER gaps. Only the actual execution/source trace of the above deterministic family-selection matcher, plus the full character-to-linear action/intertwiner bridge (existing PR #1098 owner), remain open. Avoid another custom representation/model unless the matcher returns a concrete unresolved class-map/identity.

## 25 October source-selected FULL-character implementation (strongest cut so far)

The primary Barraclough–Wilson Section 5.1 construction tensors the 729
Heisenberg extension with **arbitrary** `eta in Irr(6.Suz)`, not only the faithful
ones. The reference 6.Suz CTblLib table has 210 conjugacy classes
([Breuer/CTblLib table metadata](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/6.Suz.html)).
The original complete 3B paper and table download are linked in this ledger.

**Actual code on PR #1250:**
- The **existing** `scripts/monster_3b_suzuki_main_quotient_match.g` now
  locates all candidate outer degree156 character restrictions that are two
  distinct irreducible degree78s of 6.Suz; the faithful-78 shortcut is gone.
- For each, reuse the original 1458 main Heisenberg character, test exact
  product decomposition into degree113724, unique main -> MN3B
  full-character pullback and positive actual restricted Monster multiplicity.
  **Zero/multiple survivors cause failure rather than an invented result.**
- The selected family's faithfulness and C2 value `-90` (faithful78) versus
  `+66` (nonfaithful78) are source **outputs**.
- It now computes the precise **full 6.Suz ordinary class-function** equality
  of the selected degree78 family with both
  `Sym²(12)` and `Sym²(12)*` using the character identity
  `chi_Sym²(g) = (chi12(g)^2+chi12(g²))/2`, CTblLib `PowerMap(six,2)`,
  and `GaloisCyc(_, -1)`. Both conjugate rows must match. A C2 match is only
  a necessary screen and does not set the full equality flag.
- It records the count of pairwise equal central-C3 scalars for selected
  degree12/degree78 rows. This is **necessary** for a *common* selected
  degree729 extension descending through one diagonal kernel, NOT sufficient
  for an inertia-group or Monster linear intertwiner.
- Exact typed/JSON receipt renderer and canonical shell checker reject
  contradictory full-character counts, C2 signatures, invalid phase
  pair counts or a spurious selected-Sym² flag.
- Local backend-free Python control `scripts/test_monster_3b_suzuki_source_family_selection.py`
  exercises faithful/nonfaithful selection, ambiguity/negative controls,
  C2 vs C3 independence, full-character vs centre-only non-identity and
  paired-phase compatibility. Independent local eight-case cyclotomic
  receipt is linked in the conversation.

**Status:** these are source-written GAP/Agda and local synthetic/exact
arithmetic checks, not an executed GAP table result or kernel-checked
selected Monster action. GAP is not installed in the current execution
environment. The highest-value independent acceptance test remains the
published Barraclough/Wilson table and the actual `6.Suz` CTblLib runtime
receipt; all generic Schur/Hom/projective-normalizer proof owners are
already in PR #1098. No `mmgroup` needed for these class-function tests.

**Correction to prior paragraphs:** they describe the historical faithful-78
prefilter and its central-C2 mismatch, NOT an established Monster-selected
faithful78. The revised all-78 source-selection supersedes those statements.
