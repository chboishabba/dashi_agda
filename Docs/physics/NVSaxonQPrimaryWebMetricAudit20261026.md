# SAXON Q original paper vs vendor metrics: dated cross-PR verification (2026-10-26)

## Current primary roots checked

1. Sebastian Gemsheim, Fabian Klüpfel, Max Kneiß, Nicole Raatz, Tobias Herzig, Matthias Mendt, Evgeny Kreissig, Ulrike Rückert, Albrecht Hänel, Jan Meijer and Marius Grundmann, *Grover Search with Semiconductor Spin Qubits at Ambient Conditions*, arXiv:2609.13022, first posted 2026-09-11. The abstract reports **three nuclear spin qubits**, single-marked Grover search success **77.3 ± 3.4%**, two-marked success **87.0 ± 4.2%**, and separately states implemented universal-gate fidelities **up to 99.98%**. The latter is NOT the three-qubit algorithm success or an SXQ128 benchmark. URL: https://arxiv.org/abs/2609.13022.
2. SAXON Q, August 2026, *Orders for 128-qubit / 512-qubit quantum computers open*. The company's specification claims SXQ128 = 16 × 8 qubits/core and SXQ512 = 32 × 16 qubits/core. These are product/aggregate claims; quantum inter-core entanglement must be established separately. URL: https://www.saxonq.com/news/orders-for-128-qubit-512-qubit-room-temperature-quantum-computers-open/.
3. SAXON Q manufacturer whitepaper, *Where are we with Quantum Computing in 2026?* (2026): distinguishes classical links/circuit cutting from a quantum-mechanical connection of cores. URL: https://www.saxonq.com/wp-content/uploads/2026/04/SaxonQ-Whitpaper-QC2026-web.pdf.
4. BIPM, *The International System of Units*, 9th ed. (2019), revised 2026, DOI 10.59161/AUEZ1291. SI units/source authority is owned by `DASHI/Physics/Units/SI.agda` and its metrology bridge.
5. Diamond magnetocardiography experiment and optical sensing owner: Muhib Omar et al., *Human cardiac measurements with diamond magnetometers*, *Science Advances* eaeg5281 (2026), DOI 10.1126/sciadv.aeg5281; source/measurement details and differentiation among platforms are already kept in MCG #1238.

## Direct implementation
`NVSaxonQObservedMetricSeparationExact.agda` source-writes disjoint metrics for algorithm success, gate fidelity, photon readout fidelity, and magnetic sensitivity. Algorithm success is tied to an explicitly identified experimental register, distinguishing the three-nuclear-qubit experiment from a multicore aggregate claim. Sensitivity carries the already-owned SI calibration record; it is **not** typed as a dimensionless success percentage. The module intentionally does not instantiate made-up apparatus-specific probabilities, pulses, uncertainty laws or manufacturer-to-independent-measurement conversions.

## What the paper and existing PRs support versus what is missing
- Experimental Grover success reported by original authors: **yes** (as an attributed statement); independent raw-trace reconstruction on this branch: **no**.
- Vendor multi-core offerings: **company claims**; a demonstrated coherent 128-qubit quantum state: **not established by the reviewed evidence**.
- NV electronic spin and nuclear-spin register: **distinct physical carriers**; required hyperfine pulse and optical-transduction calibration are not supplied by the existing rational axial (DS_z^2+γBS_z) module.
- Conditional Bayes error bounds already written in #1269: mathematical readout model, **not** automatically an experimental gate fidelity, algorithm success, or MCG sensitivity.
- Exact source-written Agda type separation: **committed**, Agda kernel/CI execution: **not performed**.

## Pareto high-value next acceptance
Obtain original supplemental state-preparation/readout and gate-calibration materials for the **three-qubit** 2026 Grover experiment, pin source revision, identify actual nuclear encoding and per-shot readout measurements, and construct a same-apparatus SI-aware measurement channel using MCG #1238, SAXON Q #1270, and the NV photon observer #1269. A single experiment ID must cover state preparation, control, photon counts and correction model. The typed metric separation does not itself satisfy those evidential conditions.

Author/provenance: paper results attributed to Gemsheim et al.; company offerings to SAXON Q; standard units to BIPM; MCG human magnetometry to Omar et al.; new cross-PR classification/interface to DASHI formalisation on 2026-10-26. Reprints and derivative stories do not count as independent physical validation.
