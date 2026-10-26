# DMT TET whole-person held-out proxy comparison — original-source/Ibrahim/Pareto cut (26 October 2026)

## Actual source roots / attribution and distinct objects

- **Original phenomenology/physiology protocol and source code:** Tomás Ariel D'Amelio and collaborators, *Multimodal autonomic arousal tracks dose-dependent affective dynamics during the acute effects of DMT* (2026, **manuscript in preparation**), `tomdamelio/dmt-emotions` commit `16067a5ff31b7f390381fc5b25b587b1769d9dd1`, original `config.py` blob `620c77b4053b7001f3c0e2ce8a84ff94ba4d423a`. TET uses a **retrospective** experience trace, 15 source-defined dimensions, reported 4-second sample grid. `entity` measures a **subjective reported perception of autonomous presence**, not an independently detected agent. The original README states MIT for code and CC-BY-4.0 for a separately deposited dataset concept DOI `10.5281/zenodo.19893950`. The exact original Zenodo version, dataset file hashes, privacy/ethics scope and participant crosswalk were **not** independently inspected during this cut.
- **Theoretical endogenous M1a donor:** Mago, Deane, Sandved-Smith and collaborators (2026), DOI `10.1093/nc/niaf069`, active-inference/altered agency and precision proposal; the authors do **not** provide the little frequency-table estimator below as their fitted mechanism.
- **Existing DASHI research owners:** `Docs/receipts/DMTRestrictedModelCards20261024.json` (source blob `ccf0b117dec73f792b3e90d60f121ada80d60d44`), `Docs/receipts/DMTSteelmanDiscriminatorValue20261024.json`, `scripts/audit_dmt_research_phase.py`, `scripts/audit_dmt_tet_presence_synthetic.py` (source blob `f36f7411e142b79a4e12997825a1467ab9a77b15`), `DASHI.Cognition.ConsciousRealismDMTIdentifiabilityExact` and its DMT/Brain-IT source consumer. They already own conceptual M0, bounded endogenous M1a, flexible latent M1b, restricted M2 and source/reuse constraints. **Do not replace the existing cards or count this adapter as all four model families.**
- **Research direction and scoped implementation:** Johl Brown directed the DASHI programme; new local synthetic algorithm and regression implementation is OpenAI ChatGPT-assisted. Neither the classical Laplace count estimator nor the Brier score is an original statistical invention of DASHI. No unknown prior art is implicitly reassigned to the user.

## Implemented *consumer*, without a second generic model ontology

`scripts/dmt_tet_heldout_discriminator.py` directly imports **the existing TET validator and exact-rational codebook parser**, refuses human-record modes, and builds the 4-second one-step subjective target `entity(t+1) >= predeclared threshold` from fields observed at time `t`. Both models have prior `entity(t)` as a shared autoregressive control and share `dose`, `time`, `general_intensity`; each has seven binary covariate coordinates including three model-specific nuisance/phenomenology coordinates:

| Prototype label | Source-visible fixed features (all measured at t) | Status |
|---|---|---|
| M0 nuisance proxy | dose, relative time bin, general intensity, previous entity, pleasantness, unpleasantness, anxiety | A limited finite **baseline**, not the original complete M0 model |
| M1a endogenous proxy | dose, relative time bin, general intensity, previous entity, complex imagery, selfhood, salience | A **mechanism-motivated feature proxy**, NOT an executable active-inference generative model by Mago et al. |

Every held-out **person** is absent from training in both dose arms. Training-only conditional frequency tables receive additive-one smoothing; unseen cells fall back to a separate training-only global frequency. The output uses standard rational proper Brier scores per held-out participant and marks repeated TET windows as **not independent statistical subjects**. It does NOT assert matched effective model capacity, causal direction or blinded test-set preregistration. The two seven-field discretizations are a *nominal* capacity control, not an equal-flexibility or matched-prior proof. Its 4-second grid is retrospectively reconstructed experience and cannot be promoted to prospective instrument timing.

**Claim ceiling:** NO real participants; no original D'Amelio analysis reproduction, no measured statistical comparison, no M1a mechanistic fit, no M1b observational-equivalence defeat, no M2 fit or evidence of independently conscious agents. A better M1a proxy score would not exclude stronger endogenous latent dynamics; even a better M2 finite-fit score would not prove ontology.

## Exact test receipt

- `scripts/dmt_tet_heldout_discriminator.py`: **GitHub Git blob SHA-1 `536a47132cca4b5be3ae821b311eefbbae556684`**.
- `tests/test_dmt_tet_heldout_discriminator.py`: **GitHub Git blob SHA-1 `15cc0d80dd7367846fb959820781f0c21b9d2608`**.
- Existing imported `scripts/audit_dmt_tet_presence_synthetic.py`: **GitHub Git blob SHA-1 `f36f7411e142b79a4e12997825a1467ab9a77b15`**.

All three blobs matched exact locally executed bytes by Git object-hash calculation. `python -m unittest discover -s tests -q` in a focused local directory with these original source files returned **16/16 PASS** in 0.047 seconds. Tests cover source-synthetic admission, all-arm subject retention, order permutation, exact-fraction forecasts, no future-covariate access, past-entity shared baseline, missing/duplicated 4-second bins, source unknowns and adversarial withheld-label changes. This is a **focused source-identical execution**, not the full DASHI repository test suite, an Agda kernel run or a human-data result. No Docker image/environment or code dependencies of the original authors' study were run.

## Pareto / snowball / Ibrahim (26 October current critical path)

**Paid:** exact codebook/dose/source owner identified; previous synthetic TET onset contract reused; true participant-exclusive evaluation, shared past-entity baseline and crossfold leakage controls now executable; original source-identity and no-ontology receipts pinned. Original DMT G1 source MATLAB and pairing no-go already covered in earlier receipts; do not reproduce that work.

**P0 / highest real-world information gain:** independently inspect versioned Zenodo TET file manifests and rights/ethics/confidentiality scope (author README's CC-BY-4.0 declaration is supportive but not itself a dataset-byte receipt), participant/dose/session match, TET missingness/interpolation, original retrospective trace procedure/anchor variability, and any cohort overlap with Lewis-Healey et al. n19. Admit source rows only through a **separate audited human-data adapter**, do not silently remove the synthetic-only gate.

**P0 scientific:** replace this binary table proxy with two operational generative models using source-admitted covariates: a mechanistically constrained and independently justified M1a (counterfactual richness, sensory precision, agency priors), plus a comparably expressive endogenous latent M1b. Freeze subject-exclusive split, model complexity, scoring and missingness *before any heldout human results*. A predeclared restricted M2 must make an exclusionary prediction beyond those models or a blinded/unanticipated target-information experiment; subjective entity presence alone cannot identify external agency.

**P1 same cohort:** source-document the relationship between the D'Amelio 19-person source and Lewis-Healey 19-person TET/EEG publication; shared n/authors and nominally similar design do not prove same participants *or* an independent replication.

**P1 independent neural fibre:** continue original Niedernhuber et al. G1 real participant/time-label replay only with author `getconds` and original source-observation matrix, code version, integrity and scope. An EEG microstate is not a subjective TET `entity` field; both remain different fibres.

**Latest sibling PRs:** #1265 LILA benchmark/paired interventions, #1266 revisable observer consumer sufficiency, #1268 source-root independence and one-way ESD discipline, #1269 physical metrology source/version custody. The *method* of consumer-specific severe tests, source-deduplicated corroboration and fail-closed evidence was reused without importing unmerged sibling modules or implying Digital ESD collaborative permission (#1264 explicitly says no). The precise original scientific sources remain separately attributed.
