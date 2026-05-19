# Closure Contract Status and Next Hecke Lane

## Closed question

The current closure stack now states one thing consistently:

- the strong closure layer exposes a discharged nondegeneracy theorem path
- the downstream signature / Clifford / spin-Dirac / full-closure layers consume only the normalized-quadratic contract
- no present downstream consumer justifies widening that public contract

This means the contract-choice question is presently closed:

> downstream does not currently need null-cone reflection

That is a real result. The repo has moved from possible implicit dependence on stronger closure facts to an explicit normalized-quadratic-only boundary across the current downstream chain.

## What changed conceptually

The main gain is not a new downstream theorem. The gain is boundary truthfulness.

The stack now says explicitly that:

- strong closure knows more than current downstream needs
- bridge layers carry witness packages, but do not consume nondegeneracy
- widening would be premature without a concrete theorem that genuinely requires null-cone reflection

## What remains open

The next meaningful move is no longer "who needs nondegeneracy?" because the current answer is: nobody.

The next useful Hecke-side lane is instead:

1. test whether `profileSummaryFamily` separates any current saturated pair
2. if it does, derive the weakest projection that still separates
3. if it does not, escalate to chamber / lane-local structure rather than another scalar or already-collapsed summary

## New Agda modules in this bundle

- `Ontology/Hecke/ProfileSummaryFamilySeparation.agda`
  - general current-generator separation target over `primeImage`
- `Ontology/Hecke/CurrentSaturatedProfileSummaryFamilySeparation.agda`
  - saturated-scope specialization aligned to the current saturated branch style already used elsewhere

## Intended theorem shape

These files intentionally do not overclaim a separator.
They package:

- a separator target
- a collapse fallback
- a small record surface that makes the layer status explicit

This matches the current repo pattern of honest Layer-2 theorem surfaces.
