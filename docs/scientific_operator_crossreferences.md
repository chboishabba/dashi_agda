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

### 5. Ordered open-system balance -> metabolic source/sink accounting

`DASHI.Analysis.OpenSystemBalance` proves the pathwise identity

`Q(final) = Q(initial) + accumulatedIncrement(path, initial)`

from an exact one-event update law. Increments are evaluated in event order and may depend on the evolving state.

`MetabolicOpenSystemBalance` combines internal reactions and environmental exchange events on one typed path:

- internal reaction increments are inherited from the stoichiometric system and proved equal to zero by its left-kernel certificate;
- exchange events carry explicit state-dependent transitions and source/sink increments;
- the generic theorem gives the exact final balance.

This replaces the false choice between treating metabolism as closed and abandoning exact conservation. Closed stoichiometric invariance is recovered as the zero-exchange case.

### 6. Fejer monotonicity and contraction -> certified biological attractors

`DASHI.Analysis.FejerSublevelInvariant` owns the generic theorem:

- represent an admissible basin or region as a distance sublevel around a target;
- provide Fejer monotonicity of the transition toward that target;
- obtain one-step and finite-iterate forward invariance.

`ProteinFejerBasinBridge` instantiates that theorem for one sequence-, environment-, and attractor-indexed protein basin. It closes the `forwardInvariant` field of `ConformationalAttractorWitness` and proves invariance for every finite iterate.

`DASHI.Analysis.StrictContractionUniqueness` separately proves that an existing finite strict-contraction certificate has a unique fixed point whenever the declared strict-distance relation is irreflexive. `ProteinContractiveBasinBridge` composes the two certificates:

- the Fejer certificate supplies local basin invariance;
- the contraction certificate supplies a unique fixed conformation on the declared carrier;
- the existing protein admissibility witness establishes chemical admissibility of that fixed conformation.

The declared contraction carrier may be a local region or subtype. No global uniqueness of the ambient conformational landscape is claimed.

`CellFejerAttractorBridge` uses the same generic theorem at family level. An environment- and attractor-indexed family of Fejer sublevels constructs the complete existing `CellStateAttractor` record, including its universal `forwardInvariant` field. This keeps genome, chromatin, RNA, proteome, metabolism, membrane state, environment, and history inside the existing coupled cell carrier rather than reducing cell type to any one component.

### 7. Dissipation identity -> metabolic path monotonicity

`DASHI.Analysis.DissipationPathMonotonicity` proves that an exact balance

`F(x) = F(step(i,x)) + D(i,x)`

with nonnegative dissipation implies

`F(step(i,x)) <= F(x)`

and, by transitivity, monotonicity along every finite input path.

`MetabolicDissipationBridge` identifies the generic transition with the internal reaction step of an `OpenMetabolicNetwork`, yielding reaction-level and path-level energy descent.

The energy carrier is intentionally abstract. Thermodynamic free energy, relative entropy, or another Lyapunov quantity must be supplied by a domain theorem. The bridge does not identify physical free energy with MDL, and it does not claim detailed balance merely from monotonicity.

## Domain-neutral namespaces

`DASHI.Analysis.FiniteOperatorReductionCore` re-exports the generic kernels currently housed in the Bałaban implementation namespace:

- constrained minimizer and kernel projection;
- finite Hessian and covariance certificates;
- exact and quantitative Schur reduction;
- finite contraction certificates;
- finite Hodge–Poincaré coercivity.

`DASHI.Analysis.StoichiometricConservation` owns the reaction-path left-kernel theorem independently of any chemistry or biology namespace.

`DASHI.Analysis.OpenSystemBalance` owns the ordered source/sink path identity independently of metabolism.

`DASHI.Analysis.DissipationPathMonotonicity` owns the exact dissipation-to-descent theorem independently of a thermodynamic interpretation.

`DASHI.Analysis.FejerSublevelInvariant` owns the sublevel-set invariance theorem independently of proteins, cells, or another domain interpretation.

`DASHI.Analysis.StrictContractionUniqueness` owns the irreflexive-distance uniqueness theorem independently of the protein interpretation.

No definitions are copied.

## Highest-alpha next joins

1. **Detailed-balance discharge.** Build concrete reversible mass-action or finite Markov instances that derive the dissipation identity from forward/reverse flux symmetry and a relative-entropy functional.
2. **Atomic representation bridge.** Connect central-field eigenspaces, orbital angular momentum, spin, antisymmetric exterior powers, and Pauli occupation to shell capacities and term structure. Keep nuclear and electronic representations distinct.
3. **Fast-intermediate elimination.** Reuse Schur reduction for quasi-steady-state elimination in reaction networks and compare the effective slow generator with the full network under a quantified timescale gap.
4. **Reaction–diffusion instability criterion.** Combine spatial coercivity with the reaction Jacobian and diffusion spectrum to derive a genuine finite Turing instability witness rather than assuming `FiniteWavelengthUnstable`.
5. **Metastability and transition paths.** Add barrier and transition-state certificates so multiple protein or molecular minima can coexist without being collapsed by the local contraction theorem.
6. **Cell phenotype quotient compatibility.** Connect Fejer-invariant cell basins to the existing phenotype quotient with an explicit theorem that basin evolution preserves the selected phenotype class under declared observational equivalence.
7. **Compartment boundary composition.** Relate open-system exchange increments to selective membrane transport and prove that nested compartment balances compose without double counting internal boundary fluxes.

These are preferred over further broad “physics/chemistry/biology share a pattern” records because each produces a reusable theorem and a narrower empirical or analytic frontier.
