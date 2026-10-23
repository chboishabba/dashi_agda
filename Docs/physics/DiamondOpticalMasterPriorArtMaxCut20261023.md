# Diamond NV optical master-equation prior-art max-cut (2026-10-23)

## Repository archaeology: original owners, not duplicated inventions
1. `DASHI/Biology/Physical/FiniteChemicalMasterGeneratorExact.agda`: finite rational jump rates, Kolmogorov forward operator, and mass conservation. Source credits Gillespie (1977), DOI 10.1021/j100540a008. The new NV implementation reuses its mathematical *pattern* and identity-based proof technique, not the chemistry state's biological interpretation.
2. `DASHI/Algebra/Quantum/OrdinaryComplexQutrit.agda` and `QutritMatrixGates.agda`: ordinary complex spin-1 qutrit operators. A five-state *classical population* generator does NOT supersede quantum coherences or this prior art.
3. `DASHI/Physics/Optics/OpticalPhenomenaKernelBridge.agda`: physical propagation, material response and approximations.
4. `DASHI/Physics/Semiconductor/Device/LitavisSPADMultimodalObservationExact.agda`: source-attested SPAD counting/timing architecture; no asserted identity with actual diamond-MCG apparatus.
5. `DASHI/Biology/LiMinyongPhotopharmacologyBidiExact.agda` and `DASHI/Biology/OptogeneticMemoryObservationBoundaryExact.agda`: distinct optical biological intervention mechanisms.
6. Prior PR #1238 `NVOpticalRateSteadyStateExact`, `NVOpticalPhotonReadoutExact`, `NVPhotonBinaryLikelihoodExact`, and `NVOpticalGaugeBioEMBridgeExact`: retained as valid reduced/conditional interfaces, not incorrectly presented as full optical photophysics.

## New additions to PR #1238
`DASHI/Physics/QuantumSensors/NVFiveLevelOpticalMasterExact.agda` constructs a five-state continuous-time master generator with two ground populations, two spin-dependent excited populations, and one shelving population. Explicit pump, fluorescence, intersystem-crossing, shelving-return and microwave-exchange terms are assembled with cancellation proof of the total infinitesimal population derivative. Fluorescence prediction is derived from excited populations and radiative rates, collection gains and background.

`scripts/check_nv_five_level_optical_cycle.py` independently expresses the ten directed transitions as a matrix generator, asserts column sum zero, nonnegative off-diagonal entries given nonnegative rates, and links detected fluorescence to excited-state radiative transitions.

## Exact scope / gaps
This is a genuine finite optical Markov model that goes beyond the two-population surrogate. It is NOT the physically complete seven-level NV optical manifold or a Lindblad evolution; there are no nuclear spins, hyperfine splitting, optical excited-state coherences, singlet fine structure or actual device parameters. Infinitesimal mass conservation is not yet a theorem about positivity of the integrated time semigroup in Agda. The static photon-mean transfer does not establish independent Poisson counts without a detector process model.

Next high-alpha cuts: (1) explicit generator-level positivity / Markov semigroup and steady-state solution for parameterised subcases; (2) optical master generator to full coherent spin-one GKSL mechanics; (3) source-backed optical pump/ISC rates and experimental photodetection likelihood; (4) source-backed heart/brain magnetic field and sensor geometry. Keep mitochondrial mid-IR, neuronal opsins, and NV optics distinct, sharing experiment design rather than claiming common photophysical mechanisms.

No CI or Agda kernel execution was requested or performed. SymPy validation source committed; execution receipt not claimed. Attribution to prior NV and stochastic-process physics preserved.
