# Compact-Γ admissible preservation

This lane replaces the previous path-level assumption

```agda
∀ τ → CompactGammaAdmissible (u τ)
```

with an explicit admissible class and a reusable invariant-region theorem surface.

## Admissible class

For every selected shell `K`, `CompactGammaAdmissible` records:

- `gammaFloor ≤ Γ_K(u)`;
- `energyFloor ≤ E_K(u)`;
- `||u||_X ≤ sizeCeiling`;
- `offPacketRatio_K(u) ≤ offPacketCeiling`;
- reality preservation;
- divergence-free preservation.

`ShellFamilyAdmissible` quantifies these inequalities simultaneously over every shell marked by `UsedShell`; a fixed-shell proof is therefore insufficient unless a separate shell-selection theorem reduces the argument to one shell.

## Invariant-region decomposition

`CompactGammaPathContinuity` exposes continuity obligations for Γ, packet energy, state size, and the off-packet ratio.

`BoundaryDerivativeEstimate` exposes the inward-pointing Γ-boundary obligation. `LogarithmicModulusIntegration` exposes the integrated logarithmic-energy expenditure estimate, while `PacketEnergyPositivity` packages a strictly positive retained lower bound for packet energy.

`NoFirstExitInputs` separates the numerical margin from the analytic first-exit cost. The theorem `noFirstExit` proves contradiction from

```text
totalExpenditure < boundaryMargin
boundaryMargin ≤ totalExpenditure
```

for any alleged first exit. `FirstExitCompleteness` is the topological bridge from absence of a first exit to pathwise admissibility, and `compactGammaInvariantRegion` composes the two.

`simultaneousShellPreservation` applies this argument to all selected shells at once.

## Galerkin and compactness limit

`UniformGalerkinPreservation` requires the invariant region uniformly in cutoff `N`. `ClosedAdmissibleInequalities` isolates the lower-semicontinuity/closedness obligation needed at the compactness limit. `galerkinPreservationPassesToLimit` then transfers the full selected-shell admissible class to the limiting path.

## Authority boundary

The module proves the logical invariant-region and limit-passage composition from explicit certificates. It does **not** manufacture the Navier–Stokes estimates needed to instantiate those certificates. In particular, shell- and cutoff-uniform continuity, the inward boundary inequality, the logarithmic modulus, positive packet-energy retention, compactness convergence, and lower semicontinuity remain concrete analytic obligations.

No BKM continuation, global regularity, or Clay authority is asserted by this module alone.
