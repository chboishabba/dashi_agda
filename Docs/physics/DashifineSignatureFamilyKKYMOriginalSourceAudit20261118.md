# Original DASHIfine/dashitest signature archaeology vs KK/YM — 2026-11-18

## Attribution protocol and source boundary

**Original experimental programme:** chboishabba/dashifine; direct code/results cited by path below, and chboishabba/dashitest as related testing repo. The original authors/owners of these repositories and experimental data retain attribution. The user's prior insight was that more than the selected 3+1 signature was found before the control/selection phase. This document is a ChatGPT-assisted, source-audited *comparison*, not a discovery of Minkowski space. Historical mathematical owners: Sylvester's law of inertia, Lorentzian geometry, Kaluza–Klein circle reduction, original Yang–Mills geometry.

**Previously existing DASHI review:** `Docs/physics/Lorentz31SignatureKKYMProvenanceMaxCut20261103.md` already traced dashifine, dashitest, DASHIg, dashiQ, prior PR #70's uniqueness theorem, and numerous negative controls. Its existing original source map retains full authority. This continuation is a narrow correction to PR #1531; do not reattribute prior results.

## Verified ORIGINAL source locations in dashifine

- `26_dashi_signature_elim.py`: exhaustively enumerates diagonal masks with coefficients -1,+1 (optionally 0), signature `(p,q,z)`; computes global Q descent and an optionally delta-based forward cone with a *selected* arrow coordinate. It explicitly uses `Q(delta)<=epsilon` (timelike convention) for the cone and ranks by descent first. `--min-descent-frac=.95`, `--min-cone-frac=.95` are defaults. Selecting an arrow coordinate and a mask is not a signature-neutral physical derivation.
- `hepdata_signature_elim_rank.csv`: on **four features**, the top (3,1,0) mask `(1,-1,1,1)` and top (4,0,0) mask `(1,1,1,1)` tie for descent fraction minimum 0.833333 and mean 0.866667; their cone fraction min/mean are BOTH 0.0, so NEITHER meets the default .95/.95 gate. Numerous other (2,2),(1,3),(0,4) candidates are present. Do not promote its ranking to selected physical Minkowski signature.
- `hepdata_signature_elim_rank_allow0.csv`: admits degenerate axes; selected scores and (p,q,z) are contingent on admitting zeros.
- `hepdata_reduced4d_sig/signature_rank_reduced4d.csv`: on a different four-coordinate reduction, (3,1,0) has descent min .916667, mean .983333 and max-violation .644015; (1,3,0) and (2,2,0) have the same descent min/mean and their own different violation strengths. Several *degenerate* signatures attain 1.0 descent. This is a different reduction/criterion, not a contradictory theorem.
- `26_hepdata_mdl_fejer_closestpoint_signature.py`: FIVE-dimensional beta space `b0..b4` explicitly screens (4,1,0), (3,1,1), (3,2,0), (5,0,0), (4,0,1); constructs an actual fixed projection `P(b)=(b0,0,b2,0,b4)`, samples closest-point checks, MDL proxy and Q-cone monitors. The five-coordinate labels are NOT a measured 5D spacetime metric.
- `1_closure_out/maskedQ_signature_rank.csv`: on five beta coefficients, all-positive (5,0) scores Fejer fraction 1.0 across listed label rows whereas one-negative (4,1) varies ≈0.829–0.921 and (3,2) variants also occur. Thus observed favorable five-Euclidean screen exists but is model/criterion specific.
- `operator_analysis/signature_report.json` and `collapse_signature/signature_report_v2.json`: both explicitly record positive 5, negative 0, zero 0 for their respective fitted matrices, with their own distinct eigenvalue scales. These cannot independently prove a 5D physical Euclidean spacetime; their operators must be identified.
- `hepdata_proof_dossier/report.md`: four original selected embedding columns `v_pnorm,v_dnorm,v_depth,v_arrow`, and a separate selected three-coordinate mask (+,-,-) with 59/60 forward cone steps, one discrete violation; it directly warns against identifying this with an independently measured physical metric. The two reduced/selected tasks have different carriers.
- `26_definitive_certification.py`: a separate fitted J and discrete Lyapunov solve, followed by signature extraction and bootstrap. Lyapunov-solved positive matrices are a *dissipation/norm diagnostic*, not a physical Lorentz metric by naming.
- `26_delta_cone_signature_test.py`: separate delta-cone, not the same as Q-state descent.
- `COMPACTIFIED_CONTEXT.md`, `33_scale_robustness.py`, `29_delta_cone_signature_test.py`, `31_try_both_delta_cone.py`: earlier recovered by the existing 2026-11-03 cross-repo audit; include arrow/shape independence, reversible/bidirectional and scaled-cone controls.

`dashitest` is an accessible sibling repository (default branch main), but its code search index is unavailable. Its README references mirrored tests and the original work; a file-level complete dashitest signature inventory has NOT been performed. No fresh (5,1) dataset, named source theorem, or numerical result was recovered in this targeted search. If (5,1) denotes 5 positive and 1 negative, it requires six nondegenerate axes; it is NOT among the four- and five-axis outputs listed here.

## Verified ORIGINAL Agda owners (not new this PR)

- `DASHI/Algebra/Quantum/LorentzSignatureUniqueness.agda` (merged #70 historical owner): `ConeArrowIsotropyWitness d sign` asserts a timelike selected axis and all d remaining spacelike axes; `lorentz-signature-unique` proves equality to canonical signs, `derived-signature-is-d,1` proves (d,1). It does NOT deduce d=3 or the witness from source-neutral data.
- `DASHI/Physics/Foundations/TSFVKKSameMetricTransportExact.agda`: `SameMetricTSFVKK` requires the actual reduced KK metric ↔ same selected TSFV physical state map, equality of states, and four pointwise sign equalities; `sameMetricKKSignatureFromTSFV` obtains (3,1) *conditional on that record*. No inhabitant constructed here.
- Existing finite probes and dimension gates are mapped in `Docs/physics/Lorentz31SignatureKKYMProvenanceMaxCut20261103.md` and `Docs/roadmaps/Emergent31QuantumYMKKExactLemmaRoadmap20261103.md`.
- `DASHI/Physics/Electromagnetism/U1SU2GroupTorusExact.agda` is the ACTUAL already-constructed U1 group, inclusion to unit-quaternion SU2, and preservation of multiplication, inverses and identity. New work MUST import this owner rather than build or 'discover' another U1↪SU2.

## What signature differences physically mean

For a nondegenerate metric, `(p,q)` counts positive and negative eigenvalues; it is preserved under invertible coordinate changes by Sylvester's law. Distinguish:
1. (3,1): four-dimensional Lorentzian signature; chosen convention.
2. (4,1): five-dimensional Lorentzian signature, a natural candidate for one spacelike KK circle added to (3,1), provided the FULL reduced 5D metric is proven nondegenerate and the fibre scale positive.
3. (5,0): five-dimensional Euclidean positive definite signature, as in a Euclidean path-integral or spatial/auxiliary comparison; cannot be changed to (4,1) by a real nonsingular coordinate transformation. Analytic continuation/Wick rotation is additional analytic structure, not a real-signature-preserving diffeomorphism.
4. (5,1): six-dimensional Lorentzian signature; could restrict to (4,1) after omitting a spacelike axis and to (3,1) after omitting two, but the embedding, constraints and measured interpretation must be explicitly constructed. No independent original (5,1) screen verified yet.
5. (3,1,1), (4,0,1), (3,0,2) are **degenerate** five-coordinate masks; dropping zero directions is a quotient/restriction operation, not automatically physically valid gauge fixing.

**Pointwise exact Schur complement:** For a KK block metric with four-dimensional base g, a positive fibre square `phi²>0`, and shift A,
```
G = [ g + phi² k² A Aᵀ     phi² k A ]
    [ phi² k Aᵀ           phi²     ] .
```
Under invertible congruence the inertia is `inertia(G)=inertia(g)+(1,0)`. Therefore a Lorentzian (3,1) base gives (4,1) total; a positive Euclidean (4,0) base gives (5,0) total. This is classical KK linear algebra (Sylvester/Schur), not a derivation of the physical base signature or a new theory. It should become the *same original metric* theorem target, with actual matrix congruence and all hypotheses retained.

## Attribution-aware next exact gates

- [x] Identify prior U1↪SU2 group embedding and the conditional Agda (d,1) uniqueness theorem; no duplicates.
- [x] Retrieve actual dashifine signature scores and note multiple candidates and the failure of both (3,1) and (4,0) to meet the stringent original four-axis cone threshold.
- [x] Explicit (4,1), (5,0), degenerate five-axis candidate producers and fitted positive matrix outputs recovered.
- [ ] Find the original (5,1) six-axis result, if any, with an exact path, dataset, score, and rank/metric carrier; do not infer its existence from arithmetic possibility.
- [ ] Source-specific control matrix: original trajectory samples, arrow-selection rules, coordinate/slice masks, epsilon/threshold scales, null controls, bootstrap and sample splits for each candidate. Prove comparisons on the SAME input representation.
- [ ] Derive the selected 4D signature from independent physically calibrated clock/light-cone/observer evidence without assuming a time axis or spacelike-isotropy sign assignment in the result's premise.
- [ ] Build literal KK metric block congruence and inertia proof on the chosen original carrier; show (3,1)→(4,1) and (4,0)→(5,0), while preserving the competing interpretations until physical evidence discriminates them.
- [ ] Crosswalk 5D KK U1 circle with existing SU2 subgroup and derived SU2 chiral spin connection, without equating their curvature algebras or coupling them to the Balaban YM continuum field by labels.
- [ ] Selected original 369/YM Wilson connection, continuum RG/OS, physical 5D Einstein–matter and soliton-specific fermionic spin remain independent physical gates.
- [ ] Exact kernel and original-source script runtime receipts on pinned heads; no new Agda kernel proof claimed for this document.

**Result:** The earlier exploratory model search should be restored as competing signature candidates, with (3,1) a **conditional physically selected interpretation**, not an unconditional unique output of the original numerical signatures. This does not weaken the mathematical conditional Lorentz uniqueness lemma; it clarifies its premises and removes circular source-to-physics promotion.
