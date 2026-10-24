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
