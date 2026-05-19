# Closure Contract Status

## Closed Question

The current closure stack now states one thing consistently:

- the strong closure layer exposes a discharged nondegeneracy theorem path;
- the downstream signature, Clifford, spin/Dirac, and full-closure layers
  consume only the normalized-quadratic contract;
- no current downstream consumer justifies widening that public surface.

This closes the contract-choice question for the present repo state:

> downstream does not currently need null-cone reflection.

## What Is Established

- strong closure knows more than the current downstream chain needs;
- bridge layers carry witness packages, but do not consume nondegeneracy;
- widening would be premature without a concrete theorem that genuinely needs
  null-cone reflection.

## Open Questions

The next useful move is no longer "who needs nondegeneracy?" The current
answer is: nobody in the present downstream chain.

The active follow-up is instead on the Hecke Layer-2 side:

1. test whether `profileSummaryFamily` separates any current saturated pair;
2. if it does, derive the weakest projection that still separates;
3. if it does not, escalate to chamber or lane-local structure rather than
   another scalar or already-collapsed summary.

## Current Boundary

The discharged anisotropy and nondegeneracy theorem is available in the strong
closure surface, but the current
signature -> Clifford -> spin/Dirac -> full-closure chain factors only through
the normalized-quadratic boundary.

No present downstream contract justifies widening that public surface.
