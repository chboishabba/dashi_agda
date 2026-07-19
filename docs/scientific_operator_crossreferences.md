# Scientific operator cross-references

This tranche cross-references mathematics already proved in the repository with chemistry and biology surfaces that previously carried parallel `Set`-valued obligations.

The selection rule is strict: a cross-reference should reuse an actual theorem or prove a new domain-neutral theorem. Similar terminology or visual resemblance is not enough.

## Implemented joins

### 1. Feshbach/Schur reduction -> atomic shell locking

`DASHI.Analysis.BlockSchurCoercivity` proves a domain-neutral lower bound for

`S = D - C A^-1 B`.

`DASHI.Physics.Chemistry.AtomicClosedShellSchurBridge` treats this as the effective operator obtained after eliminating a complementary electronic subspace. A strict residual Schur gap is transported into the existing atomic `GapWitness` and `SmallRelativeToGap` obligations, yielding the existing valence-class stability theorem.

This sharpens the periodic-table frontier from the vague phrase “spectral gap to shell lock” into three auditable obligations:

1. identify the retained/complementary electronic block decomposition;
2. prove the Schur residual gap is strictly positive;
3. transport that quantitative gap into the occupied-projector perturbation theorem.

### 2. Finite constrained minimization -> molecular assembly

The Bałaban finite one-step lane already proves that its constrained minimizer has exactly the requested coarse average. `MolecularConstrainedMinimizerBridge` reuses that theorem for finite molecular configurations subject to composition, charge, centre-of-mass, symmetry, or other coarse constraints.

The generic theorem closes exact constraint satisfaction. Bonding, geometry, stereochemistry, electron compatibility, and environmental stability remain chemistry-specific witnesses.

### 3. Hodge–Poincaré coercivity -> reaction–diffusion mode control

`ReactionDiffusionHodgeBridge` reuses the finite Hodge–Poincaré estimate from the YM lane for a finite reaction–diffusion linearisation. It controls a mode norm by the identified linearized energy and packages that control with an existing Turing-mode selection witness.

The shared mathematics is coercivity of a finite differential operator after constant/constraint modes are controlled. The biological and gauge mechanisms remain distinct.

### 4. Stoichiometric left kernels -> exact reaction-path conservation

`DASHI.Analysis.StoichiometricConservation` proves the finite-path theorem once. A reaction has a stoichiometric displacement `nu_r`; a declared conservation covector `ell` satisfies

`ell(nu_r) = 0`

for every reaction. If the state quantity updates by adding `ell(nu_r)`, then that quantity is preserved by each reaction and by every finite reaction path.

Two adapters consume this theorem:

- `MolecularStoichiometricConservation` turns equality of the conserved quantity into the existing contextual molecular `conserved` relation;
- `MetabolicStoichiometricConservation` proves exact conservation for internal reaction paths in a fixed environment.

The metabolic theorem deliberately excludes external flux. An open system requires a later balance law with explicit source and sink terms rather than a false closed-system invariant.

### 5. Fejer monotonicity and contraction -> certified protein attractors

`ProteinFejerBasinBridge` identifies a protein attractor basin with a certified distance sublevel set around a basin centre. The existing generic Fejer theorem then proves that the folding update remains inside the basin.

This closes the `forwardInvariant` field of `ConformationalAttractorWitness` and proves invariance for every finite iterate. It does not claim a global folding funnel or convergence outside the certified region.

`DASHI.Analysis.StrictContractionUniqueness` separately proves that an existing finite strict-contraction certificate has a unique fixed point whenever the declared strict-distance relation is irreflexive. `ProteinContractiveBasinBridge` composes the two certificates:

- the Fejer certificate supplies local basin invariance;
- the contraction certificate supplies a unique fixed conformation on the declared carrier;
- the existing protein admissibility witness establishes chemical admissibility of that fixed conformation.

The declared contraction carrier may be a local region or subtype. No global uniqueness of the ambient conformational landscape is claimed.

## Domain-neutral namespaces

`DASHI.Analysis.FiniteOperatorReductionCore` re-exports the generic kernels currently housed in the Bałaban implementation namespace:

- constrained minimizer and kernel projection;
- finite Hessian and covariance certificates;
- exact and quantitative Schur reduction;
- finite contraction certificates;
- finite Hodge–Poincaré coercivity.

`DASHI.Analysis.StoichiometricConservation` owns the reaction-path left-kernel theorem independently of any chemistry or biology namespace.

`DASHI.Analysis.StrictContractionUniqueness` owns the irreflexive-distance uniqueness theorem independently of the protein interpretation.

No definitions are copied.

## Highest-alpha next joins

1. **Open-system stoichiometric balance.** Extend the exact internal invariant to `Q(x_final) = Q(x_initial) + sources - sinks`, indexed by external flux events and compartment boundaries.
2. **Detailed-balance free-energy descent.** Connect reversible reaction networks and Markov generators to a relative-entropy/free-energy dissipation identity without identifying thermodynamic free energy with MDL.
3. **Atomic representation bridge.** Connect central-field eigenspaces, orbital angular momentum, spin, antisymmetric exterior powers, and Pauli occupation to shell capacities and term structure. Keep nuclear and electronic representations distinct.
4. **Fast-intermediate elimination.** Reuse Schur reduction for quasi-steady-state elimination in reaction networks and compare the effective slow generator with the full network under a quantified timescale gap.
5. **Reaction–diffusion instability criterion.** Combine spatial coercivity with the reaction Jacobian and diffusion spectrum to derive a genuine finite Turing instability witness rather than assuming `FiniteWavelengthUnstable`.
6. **Metastability and transition paths.** Add barrier and transition-state certificates so multiple protein or molecular minima can coexist without being collapsed by the local contraction theorem.

These are preferred over further broad “physics/chemistry/biology share a pattern” records because each produces a reusable theorem and a narrower empirical or analytic frontier.
