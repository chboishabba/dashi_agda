## Highest-alpha continuation: native admissibility to ORIGINAL ABL (3 November 2026)

The earlier 3-bit macro code is no longer the strongest finite source. See [exact finite quantum ABL tensor calculation and full source-pinned physical max-cut](TSVFAdmissibleTensorOverlapABLMaxCut20261103.md). The new safe/source-written TSVFAdmissibleQuantumOverlapRobustnessExact and TSVFConcreteAdmissibleQubitABLExact reuse the original bidirectionally admissible histories and original TSVF QuantumSurface/ABL functions; a true two-level, length-indexed rational tensor-environment source gives overlap squared (9/25)^k and original source ABL Born weights 25^k:9^k. The exact same-source cross identity, positive denominator, original-ABL normalization, both admitted positive branch numerators and adverse-gamma counterexample are source written. **Full complex many-body Hilbert, 2017 physical gamma factors, real backward apparatus, (3,1)/OS source and Agda kernel are still OPEN.** No multiverse ontology promotion.

# TSVF macroscopic time reversibility × DASHI history fibres × multiverse BIDI

**3 November 2026 — primary literature audit and new finite mathematical source; Agda kernel pending; no physical macroscopic reverse-evolution theorem.**

## Primary literature / attribution

**Original name:** published quantum literature uses **TSVF** = two-state-vector formalism. DASHI repository owners often use **TSFV**; keep legacy names while preserving original published author terminology.

1. Yakir Aharonov, Eliahu Cohen, Eyal Gruss, Tomer Landsberger (2014), “Measurement and Collapse within the Two-State-Vector Formalism,” *Quantum Studies: Mathematics and Foundations* 1, 133–146. DOI 10.1007/s40509-014-0011-9; primary https://arxiv.org/abs/1406.6382. Proposes **classical robustness under time-reversal in one selected branch**, assuming appropriate backward-evolving terminal state and many-body environmental stability.
2. Yakir Aharonov, Eliahu Cohen, Tomer Landsberger (2017), “The Two-Time Interpretation and Macroscopic Time-Reversibility,” *Entropy* 19(3), 111. DOI 10.3390/e19030111, https://doi.org/10.3390/e19030111. Its selected-pointer robustness-ratio Eq. (25) involves surviving environment overlap and the ratio of undisturbed to disturbed degrees. This is a proposed interpretation/model, NOT experimentally confirmed macroscopic time reversal or reversal of entropy production.
3. Original Aharonov–Bergmann–Lebowitz (1964) two-boundary measurement rule; Vaidman review https://arxiv.org/abs/0706.1347. Ordinary pre/postselection does not by itself entail a physically final boundary for the entire universe.
4. Richard Corry (2025), “Finding temporal asymmetry within the many, many worlds of Everettian quantum mechanics,” *Synthese* 206, 72, DOI 10.1007/s11229-025-05166-5, https://doi.org/10.1007/s11229-025-05166-5. Independent Everettian/decoherent-history observer-selection account, NOT identical to the authors' selected single-branch TSVF ontology.

## Four distinct claims to preserve

- **Microscopic reversibility:** a closed-system dynamical law may have reversal symmetry. DASHI owner FiniteHistoryOrientationExact proves a genuine finite history involution and reversal-invariant transition action.
- **Macroscopic selected-branch robustness:** a redundant pointer/memory record may be reconstructed backwards despite disturbances to a subset of environment degrees, under a selected final boundary and suitable overlaps. This need not recover each microscopic particle's exact prior state.
- **Operational observer arrow:** an earlier accessible record lacks later information; postselected smoothing may change hidden-history inference but cannot be used to signal information into a past already recorded. HistoryWeightFiltrationExact and TSFVFiltrationArrowLorentzBridgeExact own that separate finite claim.
- **Multiverse ontology:** Everett branches, a TSVF selected outcome, counterfactual cosmological parameter values and physically realized multiple universes are four different explanatory hypotheses. Existing TSFVMultiverseViabilityCrossPollinationExact and MultiverseAttractorDiscriminatorBidiExact explicitly reject inferring a realized cosmological multiverse from the other three.

The same physical (3,1) observer may have a reversible source and a robust, selected macroscopic record **without** globally reversed entropy or a second timelike direction. Do NOT identify microscopic Theta, backward-evolving bra, macroscopic pointer reconstruction, antiunitary Lorentz time reversal, observed filtration order and Euclidean OS reflection: each needs a selected source-specific comparison theorem.

## Real 2017 physical robustness formula and its irreducible max-cut

If N environmental degrees encode one pointer result and n are subsequently disturbed, the surviving N-n degrees have branch-conditioned environmental states epsilon_1(N-n) and epsilon_2(N-n). Set
\[
q_{N-n}=|\langle\epsilon_1(N-n)\mid\epsilon_2(N-n)\rangle|^2.
\]
With appropriately normalized nonzero disturbed-factor weights Gamma_1 and Gamma_2, the qualitative source Eq. (25) has shape
\[
R=\frac{\Pr(\text{right reconstructed pointer})}{\Pr(\text{wrong reconstructed pointer})}
\sim\frac{\Gamma_1}{q_{N-n}\,\Gamma_2}.
\]
Exact gamma factor placements, positivity, the zero-wrong-probability case and normalization must be checked against the original state/operator assumptions. Large N/n is NOT enough without a small surviving-branch overlap and controlled disturbance factors.

**Physical source leaves:**
- **Q01:** actual selected Hilbert state, microscopic system, pointer and N-part environment, born from the same P01/P03 source and initial density.
- **Q02:** independently selected final boundary operator/bra with nonzero accepted probability; literal ABL/Born normalization and no-signalling.
- **Q03:** unitary/source evolution and physical pointer/environment coupling before and after n disturbances; actual overlap and gamma_i factors.
- **Q04:** rigorous exact right/wrong probability formula (source Eq.25), positivity and division, including explicit zero-wrong branch.
- **Q05:** quantified overlap upper bound, disturbed gamma lower/upper bounds and resulting R>1 or R≫1 as N/n regime grows, with correct quantifiers over disturbances and boundary conditions.
- **Q06:** an actual physical backward reconstruction on **one selected** macroscopic branch, while exact microscopic restoration may fail; show no thermodynamic entropy sign inference.
- **Q07:** match that reconstructed macroscopic observer to the same causal/metric clock and OS-reflected gauge-invariant observable sector from P02/P07, preserving the distinction between reflection and dynamical reversal.
- **Q08:** construct physical BIDI discriminators for TSVF single branch vs Everett decoherent histories vs unique law vs dynamical attractor, or explicitly retain observational underdetermination.

None of Q01–Q08 is presently demonstrated as an inhabited *physical same-object* theorem. The original 2014/2017 proposal itself is not an Agda source.

## Actual finite lemma slice (source-written)

New Golden safe module DASHI/Physics/Foundations/TSVFMacroscopicSingleBranchRobustnessExact.agda reuses original DASHI Physics Foundations FiniteHistoryOrientationExact. It contains a **three-bit redundant selected pointer with every one-site bit flip**.

- unperturbedMacroReadout: exact triple-code recovery with no fault.
- singleFaultMacroRobust: total proof for both pointers and all three single-bit faults.
- twoFaultsReverseSelectedMacro / twoFaultsDoNotPreserveOriginalPointer: sharp counterexample — exactly two flips can reverse the chosen pointer and defeat the one-error correction theorem.
- singleFaultChangesFineData: any single flip changes microscopic code content.
- firstAndLastFineDataDiffer: distinct fine fault patterns remain distinct.
- noExactMicroRestorationFromMacro: no pointer-only decoder can recover both distinct disturbed microstates sharing one macro result.
- originalPastRecordUnchanged: the **original** later-boundary choices have identical earlier accessible past.
- originalMicroHistoriesDiffer: the **original** hidden histories remain distinct.
- selectedPointersDiffer: different later boundaries select different macro branches.
- originalActionAgreesUnderReversal and microReversalInvolutive: directly reuse the **original** history theorem owner.
- selectedBranchMacroRobust: fault-correct macro value for either original later boundary.
- pastOnlyCannotDetermineSelectedMacroBranch: no function of the same past-only record correctly identifies both selected branch pointers.
- reversalAndRobustMacroCoexist: original microhistory involution and selected macro pointer robustness are simultaneously satisfied, **without** equating these maps.

This is a **finite error-correcting-code analogue** of the sourced robustness concept, not a re-proof of the physical quantum result. It does not contain real Hilbert pointers, overlapping environment vectors, 2017 Eq.25 probabilities, a physical N→∞ limit, second law, realized multiple universes, a physical (3,1) source or a Yang–Mills gap. An independently implemented equivalent finite Python check passed all six pointer/site cases, 9/9 micro-reversal histories and information-loss counterexamples. The GitHub script check_tsvf_macroscopic_single_branch_robustness.py has been pushed; it has not itself been executed against the remote head. Agda has **not** run.

## Steelman BIDI and negative controls

- **TSVF selected-branch hypothesis:** one outcome selected by both initial and final quantum states. A final state orthogonal to the chosen outcome disallows that branch; Born/ABL and no-signalling conditions must be paid.
- **Everett alternative:** decoherent coexisting branch histories and observer-selection can produce experienced asymmetry without a universal final state; its branches are not numerically identical to TSVF physically selected worlds.
- **Ordinary thermodynamic account:** time-symmetric microscopic evolution plus appropriately chosen boundary/low-entropy conditions yields a typical statistical arrow; this may explain the same observables without deriving a new 3+1 metric.
- **Multiverse/constant-attractor alternatives:** cosmological parameter viability/selection does not prove physically realized universes, nor TSVF, nor a unique microscopic mechanism. The existing DASHI source has a typed four-hypothesis coarse-observation collision.

Fault controls: two bit flips can defeat the finite 3-bit majority correction; a branch-orthogonal final condition invalidates a selected branch; no physical Hilbert overlap prevents promoting the majority model to Eq.25; a coarse past cannot determine selected fine branch; no backward signalling; a Möbius/time flip cannot create a second clock; successful pointer restoration does not prove reflection positivity, YM R443/R445/R320/R333, or a positive Clay gap.

## New roadmap phase lemmas and integration

The current 176-lemma 12-phase board is extended with **P01.L13–L19** (7 physical/finite source leaves), **P07.L15–L16** (2 same-clock bridges), and **P11.L19** (1 full explanation-family BIDI discriminator). New total: **186 unique exact lemmas**. The published quantum overlap bound Q01–Q05 remains OPEN; P01.L19 finite analogue is SOURCE written and GitHub readback is required. No existing source theorem is reattributed or silently imported from an unmerged PR. Original source-ownership and attribution retained in Docs/roadmaps/Emergent31QuantumYMKKExactLemmaRoadmap20261103.md.

Referee commands after branch integration and appropriate Agda library pin:
- python3 scripts/check_tsvf_macroscopic_single_branch_robustness.py
- agda -i . -i [agda-stdlib-path] DASHI/Physics/Foundations/TSVFMacroscopicSingleBranchRobustnessExact.agda
- agda -i . -i [agda-stdlib-path] DASHI/Unified/BalabanRGTOERegression.agda

The bracketed standard-library path above is a **user-supplied path placeholder**, not a command that has been executed. Only kernel acceptance of the selected physical source and a real many-body overlap probability calculation can close the physical time-reversal leaf.
