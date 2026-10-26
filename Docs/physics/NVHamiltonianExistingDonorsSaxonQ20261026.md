# Existing Hamiltonian audit and SAXON Q same-device NV cross-PR cut (2026-10-26)

## Latest relevant peer PRs reviewed
Agda #1270 (source-attributed SAXON Q multicore NV; Gemsheim et al. arXiv:2609.13022v2; original experimental authors distinct from commercial claims); #1269 (physical donor #1238 and electron sensor photon observer); #1262 (ideal spin-one/C3/SUSY-QM); #1261 (tetragonal group-action prior art, **not** physical diamond C3v); #1266 (generic observer collision); Lean #76/#85 (subsystem and fermionic channel methods); dashiQ #2/#3 (unmerged runtime experiment promotion).

## Hamiltonian owners actually inspected
- **Direct same-object donor**: `DASHI/Physics/QuantumSensors/NVSpinOneAxialExact.agda` (physical NV electron spin-one **axial rational spectrum** (D±γB,0)); source branch of Agda #1238. Its `AxialNV` record is imported directly by `NVElectronNuclearSameDeviceContractExact.agda`.
- **Readout donor**: `NVPhotonBinaryLikelihoodExact.agda`, normalized binary outcome with explicit nonnegativity witnesses. Reused directly; not a measured pulse-to-fluorescence response.
- **Alternative general mathematical donor**: `DASHI/Quantum/SelfAdjointGenerator.agda` is a theorem-bearing *one-point* Stone colimit generator. It does **not** establish the specific SAXON Q time-dependent NV+nuclear driven Hamiltonian; import only with a genuine same-carrier intertwiner.
- **Physical but different carrier**: `DASHI/Biology/AvianCompassSurface.agda` has fields `hyperfineHamiltonian`, `zeemanHamiltonian`, `evolve` on cryptochrome radical-pair states. This is a typed structural donor, not actual NV–nitrogen hyperfine coefficients or electronic control pulses.
- **Manufacturer-specific control source**: #1270's `Docs/papers/SaxonQPrimaryHardwareSameObjectCrossPR20261026.md` already identifies the three nuclear qubits (nitrogen-14 spin one and two carbon-13 spin-halves in the paper-specific discussion) and a future driven Hamiltonian/evolution-to-circuit witness. Preserve the named paper's priority for reported experimental operations, not this adapter.

## New same-device contract
`NVElectronNuclearSameDeviceContractExact.agda` requires source, control and optical observations to carry a common device identifier, explicitly records an axial electronic Hamiltonian and spin-labelled photon likelihood, and requires a separate nuclear-logical-to-electron-sensor level map, calibrated-control and optical-response witnesses. No specific pulse or source data are fabricated; a type inhabitation alone is **not** proof of physical implementation.

### Critical restrictions
- Same-device identifier equality is bookkeeping; it is necessary but not sufficient evidence that an experiment occurred.
- The NV electronic sensor and 14N/13C nuclear memory states are distinct. Electron ±1 spectral collision does not prove indistinguishability of nuclear memory.
- `SaxonQFiniteQutritLogicalEncodingExact.agda` in #1270 is a candidate qutrit-basis encoding, not a verified nucleus-specific register assignment.
- No claimed cross-core 128-way entanglement, physical SUSY, demonstration of quantum advantage or calibrated gate/readout fidelity follows.
- Source-written only. No Agda kernel or CI run requested or claimed.

## Pareto continuation
When branches align, make a narrow compiler consumer which takes actual isotope-specific tensor parameters, pulse schedule, selected nuclear logical subspace, calibrated time evolution, electron fluorescence response and per-shot apparatus identity from the owning modules and source artifact. Require explicit finite-dimensional channel/measurement witnesses before connecting to #1269's i.i.d. photon Bayes bounds and dashiQ experiment receipts. Keep documentary claim, source-written theorem, typechecking and measured independent replication separately attributed.
