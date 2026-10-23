# Brain-IT / DASHI BRAIN / CMS-style empirical contact — roadmap

Status: **source-written; Agda exact-head kernel receipt and independent ML replay not yet provided**.
Updated: 2026-10-24. Agda integration owner: [PR #1121](https://github.com/chboishabba/dashi_agda/pull/1121).
Sibling empirical implementation owner: [dashiBRAIN](https://github.com/chboishabba/dashiBRAIN).

## Attribution and independent objects

- **External experimental/ML result:** Roman Beliy, Amit Zalcher, Jonathan Kogman, Navve Wasserman, Michal Irani, *Brain-IT: Image Reconstruction from fMRI via Brain-Interaction Transformer*, arXiv:2510.25976v2, 2026-03-01 (ICLR 2026), https://arxiv.org/html/2510.25976v2. Related encoder: Beliy et al., *The Wisdom of a Crowd of Brains: A Universal Brain Encoder*, arXiv:2406.12179.
- **External validation benchmark:** Natural Scenes Dataset. Paper Appendix A Tables T2 (clustering) and T3 (number of clusters); Appendix B Table T7 (subject 1, 15/30/60-minute transfer).
- **Repo-original formal consumers and obstruction:** `DASHI/Biology/NeuralRepresentationLaplacianExact.agda`, `DASHI/Core/CoarseFineFabricCalculusExact.agda`, `DASHI/Physics/Foundations/CoarseObservableFactorisationBidiExact.agda`, `DASHI/Biology/BrainITConsumerRelativeExact.agda`. They are finite mathematical models, not paper-derived neuroscience measurements.
- **Experimental-provenance *method* only:** CMS HEPData t43/t44 freeze, `DASHI/Physics/Closure/HEPDataCMSBelowZDrellYanClaimExact.agda`; `CMSCoarseObservableContactBidiExact.agda`. These are **particle physics** measurements, not brain data or a biological model. Reuse their typed-source / independent-replay / claim-gating discipline only.
- **DASHI BRAIN:** Drosophila connectome, kernel defect, local-vs-coarse structure, optical calcium functional imaging, behaviour/effector registration. **Fly optical calcium != human BOLD fMRI**. Structural graph edges != learned Brain-IT clusters. No dataset-level identification is made.

## Results completed in this cut

1. **Correct primary-source attribution**: 15-minute meaningful reconstructions are reported by the primary paper. Table T7 gives 450 fMRI samples on subject 1; PixCorr .336, SSIM .476, CLIP identification 91.3%. Do not extrapolate to arbitrary thoughts/dream reading.
2. **Concrete consumer-relative nonfactorisation**: the existing neural-state example has two distinct microstates with identical coarse fMRI-like observations and differing Laplacian variation. `BrainITConsumerRelativeExact.agda` instantiates the repo-original generic collision theorem to refute **any universal exact decoder** of that consumer from that projection. Conversely, the declared coarse observation itself trivially factors. This is not proof that Brain-IT cannot reconstruct the visual features it targets.
3. **Typed published-value transcriptions** in `BrainITTableReceiptsExact.agda`: Table T7 subject-1 15/30/60-minute results; Table T2 functional / coordinate / Schaefer-400 / Schaefer-1000 clustering; selected Table T3 counts. Integers are normalized in thousandths, without floating-point equality claims.
4. **Cross-lane registration**: `BrainITValidation.agda` imports the connectome weld, consumer theorem, published metrics, and promotion gates. `DASHI/Biology/Everything.agda` exports owners.
5. **Metric nuance**: Table T2 3D-spatial-clustering SSIM 0.491 > functional-clustering SSIM 0.486, even though functional outperforms coordinate clustering on pixel correlation 0.386 > 0.378. No universal metric-wise dominance is claimed. T3 128 clusters are a *hyperparameter*, not a physical law; at 512 clusters PixCorr is 0.392 vs 0.386.

## Research target and same-object diagram

Let `X` be a fine latent system, `Q : X -> B` a measured observation, `T : X -> Y` a declared consumer, and `D : B -> Y` a decoder.

- Exact retention: `T = D ∘ Q`.
- Necessary condition: `Q(x)=Q(y) => T(x)=T(y)`.
- Concrete collision: `Q(x)=Q(y)` while `T(x)!=T(y)` refutes universal factorisation.
- *Do not assume* a right-inverse section of an arbitrary fMRI map. The generic split-projection converse is explicitly conditional on a supplied section.
- Paper stimulus-label `S`, fMRI `B`, learned V2C `C`, semantic / low-level features `Y_sem, Y_low`, and final diffusion image `I_hat` are separately typed. `B->I_hat` does not invert `X->B`.
- Proposed empirical DASHI commutation diagnostic: `distance(Q(Kx), K_Q(Qx))` for a **declared**, dataset-specific `K`, coarse `K_Q`, matched partition, and observation metric. Its value is not currently known.

## Acceptance and remaining burden (prioritised)

| Priority | Next deliverable | Exact owner / acceptance | Current |
| --- | --- | --- | --- |
| P0 | Exact-head typecheck of new Agda modules | `agda -i . DASHI/Biology/BrainITValidation.agda` in the repository's pinned Agda/standard-library environment; check `Everything.agda` as feasible | **Unverified** |
| P0 | Static source/contract regression | `python -m pytest -q tests/test_brainit_fmri_maxcut.py tests/test_brainit_connectome_weld.py tests/test_brainit_consumer_receipts.py` | Source-written; no fresh local test receipt |
| P1 | Frozen independent Brain-IT evaluation | Revision-locked NSD subject, train/test stimuli split, exact per-subject preprocessing, predicted fMRI augmentation policy, checkpoint hash, evaluator hash, metric version and image outputs; reproduce T7 or state discrepancy | Not executed |
| P1 | Actual functional/structural quotient experiment | Same held-out stimuli, matched cluster budgets, functional V2C vs spatial, Schaefer, random and degree/locality controls; each metric and uncertainty reported separately | Hypothesis only |
| P2 | Kernel commutation/retention audit | `dashiBRAIN` finite audit module on declared example, then same-object evaluation on real registered recordings. Test `QK vs K_QQ` explicitly | Toy protocol, no NSD coupling |
| P2 | Modality and species transfer | Separate fly calcium/voltage, human BOLD, anatomical registration and neurovascular coupling; no unsupported cross-species identity | Open |
| P3 | Interpretability beyond attention heatmaps | Held-out perturbation / occlusion probes, functional cluster interventions, channel-specific feature-separation metrics and subject-split stability | Open |

## Failure-mode gates

1. A published number frozen in Agda is **not** kernel recomputation of the ML metric.
2. A typed string digest field without actual data/checkpoint bytes is **not** independent replay.
3. Near-accurate images may reflect learned generative priors as well as measurable stimulus information.
4. Brain-IT functional clusters are learned shared decoder coordinates; they are neither anatomical edges nor demonstrated full neuronal microstates.
5. A finite toy counterexample is a general model-theoretic firewall, not a physical universal impossibility theorem about all stimuli, observers or measurements.
6. CMS Drell–Yan values cannot validate a neurological model; only the provenance/consumer-retention methodology cross-pollinates.

## Done when

**Formal cut:** exact-head Agda validation is green, tests pass, upstream metadata is source-correct, and the merged owner remains discoverable in `Everything.agda`.

**Empirical cut:** subject/checkpoint/test-split identities are digest-bound; T2/T3/T7 comparisons are independently reproduced (or failed/revised with signed receipts); matched-baseline quotient results include ablations and uncertainty. No stronger promotion before then.
