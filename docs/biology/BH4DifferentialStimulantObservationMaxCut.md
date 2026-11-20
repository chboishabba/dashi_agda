# BH4 differential stimulant observation — Pareto cut (2026-11-20)

Status: synthetic finite countermodel, source-written; Agda exact-head kernel acceptance OPEN. Not a clinical subtype, treatment recommendation, measured flux, fitted drug model, or original 29x12 source payment.

## Attribution and provenance
- Kimberly Kitzerow owns her documented proposed redox/allostatic BH4 allocation synthesis, not all older enzyme biochemistry. Source: https://www.researchgate.net/publication/383021907_The_BH4_Pathway_as_an_Allostatic_Mechanism_in_the_Pathology_of_Autism_and_Systemic_Comorbidities (version/date and exact original passage pins remain review obligations). The public author page https://www.kimberlyedu.org/the-bh4-shunt is a separate manifestation, not evidence of priority.
- Original biochemical investigators own their findings; the 2020 consensus guideline https://doi.org/10.1186/s13023-020-01379-8 synthesises evidence for BH4-dependent monoamine synthesis; Faraone's 2018 review https://doi.org/10.1016/j.neubiorev.2018.02.001 synthesises stimulant pharmacology. Neither establishes this candidate causal mechanism.
- Kay et al. https://doi.org/10.1016/j.cell.2025.11.039 own the network-level arousal/reward imaging findings, not BH4 evidence. The precision trial uses methylphenidate, not a BH4-stratified head-to-head comparison.
- https://www.instagram.com/reel/Df8V7Y6N9mE/ is the trigger, a user-supplied transcript of the creator's hypothesis; creator identity, exact manifestation and time coordinates remain unverified. No patient data or clinical authority admitted.
- DASHI contributors retain existing geometry, countermodels and implementation priority; this new finite construction is assistant implementation assistance within that programme; no priority claim for pharmacology or clinical science. Rhea/ChEBI and other databases retain curation credit; original experiment authors retain scientific credit.
- Scientific support, priority/chronology, and contact/exposure are independent tracks. Citation is not proof, support is not priority, priority is not correctness, exposure is not derivation/plagiarism, unpaid is not zero, Pareto rank is not truth rank. Preserve source-coordinate, manifestation, context, estimand and source-role matching.

## Minimal construction
Reuse BH4CatalyticTurnoverFutureCountermodelExact.CatalyticCapacityScenario. Capacity = pool * turns; realised synthesis + unused capacity = capacity. Initial accessible reserve + realised synthesis = basal release + extra release + final reserve. No BH4 molecule is consumed per synthetic turnover count. The reserve represents a lumped monoamine stock, not a source-paid vesicular kinetics model.

The fixed illustrative observation is (r/2, r, r+a), scaled by 2 in Agda, with r basal release and a additional mobilisation. The three challenge observations are counterfactuals with common starting state, not sequential doses. The stock balance pays the maximum-release window. Clearance 2/1/1 is synthetic and not a pharmacological parameter or dosage. The model omits NET, receptor sensitivity, metabolism, clinical effects, feedback and explicit vesicle/cytosol compartments.

| pool | turns | synthesis | unused | initial reserve | basal | extra | final reserve |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 1 | 0 | 3 | 1 | 1 | 2 |
| 2 | 1 | 2 | 0 | 2 | 1 | 1 | 2 |
| 2 | 2 | 1 | 3 | 3 | 1 | 1 | 2 |

All yield the scaled observation (1,2,4). The first two differ in pool and synthesis; the first and third have the same synthesis and different pool. Exact rational fixture arithmetic independently checked locally (3/3); no Agda kernel or exact-head aggregate run claimed. This proves a source-written non-factorisation in the selected toy model, not non-identifiability for every physiological model or a proof that BH4 is irrelevant.

## Pareto continuation
S1 (source-written): pool and synthesis non-factorisation, import focused root.
S2 OPEN: compartment-resolved TH to L-DOPA to DA and DBH to NE, QDPR/redox recycling, independently sourced same-object stoichiometry and units (reuse original owners; don't alter the 29x12 chart).
S3 OPEN: conserving cytosolic/vesicular/extracellular balances, DAT/NET direction, degradation, explicit time-indexed challenge and washout; no invented zero exchange.
S4 OPEN: compare allocation against recycling, redox, transport, independent enzyme regulation, reserve depletion, receptor/PK and stress histories; use actual estimand-specific observer receipts and held-out responses.
S5 OPEN: source-paid spatial/PNP attachment, exact-head local Agda/parallel_checker, independent empirical discrimination. No clinical promotion.
Existing P0-P3 and L01-L12 gates are unchanged. Prioritize source and measurements that split the collision, not a stronger unneeded model.
