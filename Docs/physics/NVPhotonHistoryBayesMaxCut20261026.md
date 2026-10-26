# NV quantum observation: finite-history and Bayes-risk max-cut, 2026-10-26

Canonical owners: diamond MCG #1238 for axial energies/ODMR and normalized photon likelihood; stacked #1269 for same-object C3/qutrit label weld, energy collision, single/two-shot distributions and all-depth tree normalization. Earlier finite probability/binomial work and statistical evidence core are prior art; no competing probability framework is introduced here.

New source:
- `NVPhotonHistoryFiniteSumExact.agda`: explicit enumeration of all finite click/dark histories and rational mass sum using the previously declared history likelihood. The equality between explicit list sum and normalized tree mass is still a separately identifiable proof obligation; do not cite it as kernel-checked.
- `scripts/check_nv_photon_history_bayes_exact.py`: standard-library exact Fraction exhaustive finite i.i.d. enumeration with equal-prior Bayes error = 1/2 sum_h min(P(h|+),P(h|-)). Checks normalization, state-exchange symmetry, identical-response error 1/2, and monotone non-increasing Bayes error with an additional outcome for n=0..7 on a 6x6 grid of rational probabilities. This is algorithm-level finite computation, not an Agda theorem or a measured device result.

Decision theory: if single-shot photon responses coincide, all independent-repetition history distributions coincide, giving minimum equal-prior Bayes error 1/2. Distinct responses can improve aggregate discrimination, but the exact error depends on n and overlap. For p+=4/5 and p-=1/5, the illustrative optimal error is 1/5 at n=1, 1/5 at n=2, and 13/125 at n=3. Even n has ties and need not strictly improve. These probabilities are synthetic examples, never measured NV photon contrast.

Physical promotion requires independently justified trial-condition model: prepared spin state reset/re-pump, laser/microwave pulse timing, detector dead time, spin backaction, drift and readout windows, calibration and prospective held-out data. Existing dashiQ #2/#3 controls experiment receipts and promotions. No inference of vendor 16x8 cross-core entanglement, physical spin-level C3, spacetime SUSY, quantum advantage or magnetocardiography fidelity.

Source-written Agda remains kernel-pending; CI intentionally out of scope. Distinguish exact Python regression from a mathematical proof across all rational parameters, and both from real-world measurement.
