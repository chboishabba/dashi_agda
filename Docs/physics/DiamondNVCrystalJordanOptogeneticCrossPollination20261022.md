# Diamond NV crystal symmetry / Jordan-algebra / optogenetic cross-pollination
Date: 2026-10-22

## Priority decision
Keep the diamond-MCG NV optical sensor, mitochondrial spectroscopy, and optogenetic causal intervention in scope. Do not escalate to speculative nonabelian KK or exceptional-algebra claims without a physically derived same-object map.

## Existing verified-in-repository owners
- `DASHI/Algebra/Quantum/OrdinaryComplexQutrit.agda`: constructed real/complex qutrit star algebra; preferred starting point for concrete spin-1 Hamiltonians and Hermitian operators.
- `DASHI/Physics/CondensedMatter/AltermagnetCrystalActionBridgeExact.agda`: concrete two-sublattice C2 spin/momentum symmetry, but NOT a measured NV diamond point group. Reuse *methodology* of finite group action, not its physical identification.
- `DASHI/Physics/Closure/UnificationJordanVonNeumannAdapterBoundary.agda`: Jordan–von Neumann polarization/parallelogram-to-inner-product programme, with open promotion requirements. This is **not** exceptional Albert/Jordan algebra.
- Agda PR #1106, Albert/F4 first-Tits and trinification: candidate exceptional-Jordan structural donor, not direct diamond NV defect physics.
- `DASHI/Biology/Levin/MitochondrialCristaOscillatorBoundary.agda`, `MitochondrialCoupledOscillatorModel.agda`, and PR #1238's Mitopolariton* modules: candidate mitochondrial spectroscopy and energy-metabolism experiments.
- `DASHI/Biology/OptogeneticMemoryObservationBoundaryExact.agda` and `DASHI/Physics/Measurement/CausalBioelectromagneticExperimentExact.agda`: optical intervention and biological observation separation.
- PR #1239 `KaluzaKleinGaugeShiftExact.agda` imported into #1238. It provides horizontal 1-form gauge invariance, not a validated five-dimensional biological mechanism.

## Scientific sensor owner that needs implementing
The diamond NV electron ground state has an S=1 manifold. The natural Hamiltonian is, schematically,
 H = D S_z² + gamma (B_x S_x+B_y S_y+B_z S_z)
     + E (S_x²-S_y²) + H_hyperfine + H_noise.
These S matrices must be realized in the *existing* concrete complex qutrit package and proved Hermitian under explicit real parameter assumptions. Crystal defects and strain determine D,E and relevant axes; one may not import a different compound's symmetry without a homomorphism and site/defect identification witness.

The physical path is
 diamond crystal / NV defect orientation and strain
  -> spin-1 Hamiltonian / resonance energies
  -> optical pumping and microwave interrogation / photon likelihood
  -> magnetic field projection from cardiac or neural currents
  -> statistically calibrated experiment.

## Causal biology cross-pollination
The bioelectric counterpart is independently:
 mid-IR illumination + optogenetic channel control -> mitochondrial metabolism,
 membrane-current dynamics, neural population field and observed outcome.
Keep mid-IR mitochondrial spectra distinct from visible-light opsins and NV optical fluorescence. Shared *experimental design and inference* is useful; coupling between these regimes is a testable hypothesis, not an established transfer theorem.

## Immediate formal deliverables
1. Crystal-site point-group and NV-axis orientation package with exact action witnesses and a scoped strain-tensor invariant.
2. Concrete constructive-complex 3×3 spin-1 matrices (including off-diagonal transverse Zeeman terms) and H=H† proof.
3. A physical magnetic projection and optical ODMR likelihood with normalized probabilities and linewidth/shot-noise assumptions.
4. Measurement error and distinguishability: vector sensor configurations versus one-axis degeneracy; thermal/RF/vibration controls.
5. Optogenetic experimental factorial contrasts using actual biological source parameters, with explicit mechanistic competing hypotheses.
6. Use Jordan–von Neumann only for justified inner-product/polarization construction; exceptional Jordan/Albert only if a concrete representation of relevant NV/molecular observables is supplied.

## Distinctiveness and attribution
Established spin physics, crystallography, classical Maxwell theory, KK and prior mitochondrial/optogenetic experiments belong to the original literature. Current DASHI owners are preliminary formal building blocks, not a derived physical-unification result. Source-written modules are not automatically kernel-checked. No CI was requested.
