# Diamond NV physical-observer cross-pollination (2026-10-26)

## Current peer-PR review
This note accompanies stacked diamond MCG quantum PR #1269. We searched the most recently updated PRs in `dashi_agda`, `dashi_lean4`, and `dashiQ`. The immediately relevant parallel work:
- **Agda #1266**: revisable observer and consumer factorization collision obstruction. Method reused here with a *literal NV axial-energy producer*; no import of unmerged source, and no claim the generic proof belongs to this PR.
- **Agda #1267**: severe tests, falsification design and provenance; methodological roadmap only, not a physical-data source.
- **Agda #1261**: tetragonal D4h certificate and crystallographic class catalog. Cannot import its D4h action as the cubic-diamond `O_h` or NV-site `C3v`.
- **Agda #1260**: exact C3 character/cyclotomic and ramified phase transfer; discrete phase representation is not identical to physical NV spin or optical path interference.
- **Agda #1262**: separately developed NV spin-1/C3/SUSY-QM algebra and finite spin-level Hamiltonian obstruction. Avoid duplicating physical NV definitions already owned by parent MCG #1238.
- **Agda #1238**: owns actual NV rational axial energy, sensor crystal-axis carriers, optical photon/rate evidence, MCG calibration and TSFV optical observation. This branch is stacked directly on that owner.
- **Lean #76/#85**: partial trace, quantum subsystems and channel methodologies require a typed physical representation weld.
- **dashiQ #2/#3**: MDL decision and experiment receipt consumer owners; do not silently promote device claims from source transcript.

## New exact same-object theorem on #1269
`NVMCGQuantumEnergyObserverCollisionExact.agda` consumes `NVSpinOneAxialExact.energy` and the chart `NVMCGQuantumComputingSameObjectWeldExact.levelEnergy`. At axial field B=0, the two distinct labels m=+1 and m=-1 have precisely the same rational energy D. Hence there can be no function `decode : ℚ → C3` such that `decode (energy x) = x` for all three spin labels. This is a genuine consumer-relative nonidentifiability theorem for the existing physical *model*, not a synthetic generic collision.

The theorem **does not** say real NV spin readout is impossible: richer observations (spin-selective optical signals, microwave excitation, field bias, repeated experimental context) may separate the states, if their physical measurement contracts and data support it. An outcome distribution must be checked against the actual instrument and experimental protocol; MCG sensitivity numbers are not readout or quantum gate fidelity.

## Next Pareto discriminator
Choose one platform-specific instrument and predeclare: state preparation, laser/microwave sequence, axial field magnitude, directional orientation, raw photon count/time streams, dark/background counts, repeated trials, nuisance drifts, inference model and held-out validation. Test conditional identifiability of the two spin states under full data and an energy-only baseline. Reuse the parent diamond readout/channel contracts and dashiQ experiment receipts when their branches become compatible.

### Proof and attribution status
The code is source-written; no Agda compiler or CI was run or claimed. Quantum observer separability must not be confused with claiming cross-core entanglement, NV hardware advantage, spacetime SUSY or a measured magnetocardiogram. Earlier author/source ownership remains in the imported modules and peer PRs.
