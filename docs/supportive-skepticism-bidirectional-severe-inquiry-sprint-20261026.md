# Sprint roadmap: charitable bidirectional severe inquiry (2026-10-26)

Status: **working research protocol / cross-pollination roadmap only**. This document does not certify empirical claims, change other repositories, include work in the Digital-ESD team corpus, or assert an Agda kernel proof.

## Purpose and governing attitude

For a claim `H` that an apparatus or intervention exists and does `X`, begin with **the strongest physically and historically coherent version of the actual claimant's hypothesis**. Independently develop the strongest alternatives, then seek an intervention and measured observation that distinguishes them. An unanswered question remains unresolved, not refuted. Absence of expected evidence can support rejection *only conditional on a sufficiently sensitive and independent opportunity to observe it*. Precedent is evidence, not a logical boundary on possibility.

There are two separate outputs: (a) the highest-efficiency/strongest supported reconstruction that could actually work, and (b) an evidence-based adjudication of the claimant's stronger assertions. Neither substitutes for the other.

This is a synthesis and roadmap, **not a novel discovery**. Attribute critical rationalism to Karl Popper; progressive/degenerating research programmes to Imre Lakatos; severe testing to Deborah Mayo; abduction to C. S. Peirce; Bayesian predictive/model criticism to its respective authors; and specific experiment-design, adversarial collaboration, causal intervention, and information-theoretic contributions to their original sources.

### Indigenous epistemic provenance / non-assimilation

Etuaptmumk / Two-Eyed Seeing originates in Mi'kmaw knowledge and teaching, advanced by Elders Albert and Murdena Marshall with Cheryl Bartlett and others. It is **not** an alias for the generic claim-testing framework. Preserve Indigenous authority, relational context, reciprocity, and distinct standards of warrant. Do not unilaterally import this draft into team-governed Digital-ESD work. Cross-links are invitations for review, not promotions or reinterpretations.

## Prior-art reuse in this repo (verified file paths on the default branch)

- `DASHI/Core/ProofSearchFrontierObserverTrustExact.agda`: actual vs reported vs believed frontier, explicit provenance; do not mistake stale/claimed closure for actual closure.
- `DASHI/Core/ProofSearchLeastPrivilegeAdmissionExact.agda` and `DASHI/Core/ObservationInterventionTrustFibreExact.agda`: admission and intervention trust boundaries.
- `DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda`: experiment-design scaffold.
- `DASHI/Wikimedia/IbrahimPesticideExperimentDesignRegression.agda`: experiment-design regression; inspect and reuse, do not invent another incompatible selector.
- `docs/digital-esd-source-ingestion-proof-search-addendum.md`: source-local evidence ceilings: provenance != reproducibility != extraction correctness != empirical support != claim truth. **Reference only; no manuscript inclusion.**
- `docs/superpowers/specs/2026-09-17-distributed-epistemic-fabric-attribution-design.md`: attribution integration precedent.
- External repo contracts to *reference, not edit*: SensibLaw `docs/sourcing_attribution_ontology_20260213.md`; ITIR-suite `docs/planning/evidence_attribution_frame_contract_v2_20260212.md` and `graph_epistemic_neutrality_contract_20260212.md`.

## Current PR cross-pollination candidates (discovered 2026-10-26; **not modified**)

1. [#1266 Revisable observer consumer no-go and source-first proof-search roadmap](https://github.com/chboishabba/dashi_agda/pull/1266): reuse actual/reported/believed frontier distinction, negative-result ceilings, and revisable observer status.
2. [#1263 Physics: source-attributed teleportation/PK experimental discriminator max-cut](https://github.com/chboishabba/dashi_agda/pull/1263): strongest positive physical model vs nuisance, exact experiment and causal discriminator.
3. [#1262 NV spin-one × C3 × finite SUSY-QM](https://github.com/chboishabba/dashi_agda/pull/1262): quantum carrier and physically typed observation gates; **do not treat structural reuse as an MG10 mechanism**.
4. [#1265 ML Dust/Noise × Sophontic paired perturbation and Walsh credit](https://github.com/chboishabba/dashi_agda/pull/1265): paired perturbations and evidence-relative credit.
5. [#1252 Psychotronics: Hardt delta maximal physical and nonlocal steelman](https://github.com/chboishabba/dashi_agda/pull/1252): positive steelman plus nonlocal constraints.
6. [#1243 Conscious realism × DMT kernel identifiability, trace audit, attribution max-cut](https://github.com/chboishabba/dashi_agda/pull/1243): identifiability and source-typed claims.
7. [#1249 Hyperfabric signed-zero/wave finite cut](https://github.com/chboishabba/dashi_agda/pull/1249): retain algebraic evidence separately from physical interpretation.
8. [#1261 Exact tetragonal 4/mmm symmetry](https://github.com/chboishabba/dashi_agda/pull/1261): material/symmetry parameter consumers only once justified.

Links identify plausible consumers from PR titles. Their precise branch implementations and mergeability are **not claimed audited** by this roadmap. Consult actual diff before merging or reusing.

## Formal object / proposed Agda sprint, not yet implemented

```text
Claim {
  original_source_root; attributed_actor; relayer; dated_artifact;
  proposition; claim_scope; asserted_performance; physical_boundary;
}
Model { hypothesis; resource_inventory; assumptions; parameters; predictions; provenance; }
Test {
  intervention; measurement; instrument_resolution; nuisance_set;
  candidate_model_predictions; controls; sensitivity; independent_replications;
}
Verdict = supported_under_conditions
        | contradicted_under_conditions
        | unresolved
        | measurement_or_model_mismatch
```

Required links: `ATTRIBUTED_TO`, `DERIVED_FROM`, `SUPPORTS`, `CHALLENGES`, `DISCRIMINATES`, `SUPERSEDES`; source roots and repetitions must not be counted twice. Contradiction must specify tested parameter and confidence range.

Potential Agda lemma targets:
- Repeating a source cannot increase the number of independent source roots.
- A failed test with zero sensitivity imposes no negative claim promotion.
- Changing a claimant's claim scope requires a new claim/version edge.
- An energy-balanced cyclic device with zero incoming work and nonnegative losses cannot export positive net work *under precisely enumerated closed-system assumptions*.
- A one-way FET/inductor switch can route and retain current without being itself an unaccounted energy source; include switch, gate driver and stored magnetic energy.
- Independent new data may revise the result in either direction; no automatic promotion from structural/quantum analogy to physical effect.

## MG10 worked example: actual scientific target

**Claim root:** Tripp/Infinity SAV USA documentation alleges autonomous net electrical energy through spin physics; separately attribute Andrii Slobodian's hardware development; separately attribute GAIA participant testimony; Instagram is a reporting node, not a second experiment.

Hypotheses to compare:
- H1 finite rotor/capacitor/magnet/spin storage;
- H2 externally supplied/recirculated power or environmental work;
- H3 conventional machine with FET/choke synchronous extraction and efficiency improvements;
- H4 nonequilibrium quantum/spin-bath engine with quantified free-energy input;
- H5 genuine reproducible unexplained energy residual;
- H6 faulty measurement, waveform/power-factor or narrative extrapolation.

**Never conflate:** spin-generated AC / high internal reactive power / coherence advantage / low FET switching overhead **with** autonomous kilowatt net output.

For an observation interval `[0,T]`, measure simultaneous signed real electrical/shaft/thermal/resource power; rotor speed/inertia; internal battery/capacitor/inductor state; all external inputs. Evaluate
```text
R = E(T)-E(0) + W_load + W_losses - W_external
```
with instrument and model uncertainty. Conservation predicts `R≈0` for the complete accounting boundary. A statistically positive residual is an **anomaly**, not attribution to a quantum source without a causal experiment. A strong null result bounds specified mechanisms only at its achieved sensitivity.

For full candidate steelman, optimise the conventional phase-selective rectifier FIRST, then add collective spin coherence/LLG or finite quantum spin-bath coupling with reciprocal reaction torque and energy accounting. Candidate quantum enhancement: difference under matched driving/resource budgets, not comparison with a poorly tuned classical controller. Look for distinctive spectral/control correlations, reproducible on/off interventions and quantitatively supported kW scaling. No claim of physical MG10 calibration is justified without primary waveforms/specifications.

## Max-cut / Pareto ordering

P0 source root + evidence graph + PR actual-diff reuse audit; P0 design mutually exclusive prediction table with power-meter sensitivity and missing-observable flags; P1 optimise baseline FET/choke/rotor energy inventory against original 2017 75 Wh / 222 Wh claims; P1 finite nonequilibrium spin-bath engine + explicit recharge/work reservoir; P1 paired intervention and model selection; P2 Agda bridge of source-root independence and no-go *conditional assumptions*; P3 hardware replication only if dimensions, BOM and metering available.

### Acceptance and non-promotion

- `documented` != `independent confirmation`; `working code` != `Agda kernel checked`; `source citation` != `experimental reproduction`; `historical death` != `causal suppression`.
- All source-based claims attach to original authors and primary artifacts where available.
- Any novel computational design/test from this sprint is attributed to this investigation and contributing authors, **not retroactively to historical claimants**.
- Preserve honest unresolved outcomes. Never use lack of imagination, novelty, theoretical familiarity or mere citation counts as a substitute for a discriminating test.
- Cross-repo targets above are proposals only; no unauthorized Digital-ESD team integration.

Sprint deliverable: **this standalone roadmap document only**. Existing Agda proofs and other repositories remain untouched; no CI/Agda kernel verification is claimed.
