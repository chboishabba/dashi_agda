# Scientific operator cross-references

This tranche cross-references mathematics already proved in the repository with chemistry and biology surfaces that previously carried parallel `Set`-valued obligations.

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

## Domain-neutral namespace

`DASHI.Analysis.FiniteOperatorReductionCore` re-exports the generic kernels currently housed in the Bałaban implementation namespace:

- constrained minimizer and kernel projection;
- finite Hessian and covariance certificates;
- exact and quantitative Schur reduction;
- finite contraction certificates;
- finite Hodge–Poincaré coercivity.

No definitions are copied.

## Highest-alpha next joins

1. **Stoichiometric left-kernel theorem.** Formalize species-by-reaction incidence, prove that every left-null vector is conserved along arbitrary reaction paths, and instantiate molecular and metabolic `conserved` fields.
2. **Detailed-balance free-energy descent.** Connect reversible reaction networks and Markov generators to relative-entropy Lyapunov descent without identifying thermodynamic free energy with MDL.
3. **Protein folding contraction/Fejér bridge.** Replace attractor-only fields with a conditional theorem from an environment-indexed contraction or Fejér certificate to basin invariance and uniqueness within the certified region.
4. **Atomic representation bridge.** Connect fermionic shell occupation to the existing Clifford/spin and SU(2)/SU(3) representation lanes, while keeping nuclear and electronic representations distinct.
5. **Fast-intermediate elimination.** Reuse Schur reduction for quasi-steady-state elimination in reaction networks and compare the resulting effective generator with the full network under a quantified timescale gap.

These are preferred over further broad “physics/chemistry/biology share a pattern” records because each produces a reusable theorem and a narrower empirical or analytic frontier.
