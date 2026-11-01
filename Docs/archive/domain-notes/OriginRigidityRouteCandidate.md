# Origin Rigidity Route Candidate

Declared surface level: `candidate/governance`.

This document records a candidate internal route for W8 origin/rigidity. It is
not a promotion receipt and does not change the current W8 status.

## Candidate Route

The route being recorded is:

1. identify the DASHI spine structure group as `E8` or as a semisimple
   extension that contains the Standard Model route;
2. prove semisimplicity for that structure group;
3. instantiate a Whitehead-style cohomology-vanishing theorem;
4. derive first-order rigidity of the spine algebra;
5. bridge first-order rigidity to a candidate origin-uniqueness statement;
6. compare that candidate against the current W8 origin-promotion receipt
   shape.

The corresponding Agda surface is
`DASHI.Physics.Closure.OriginRigidityRouteCandidate`.

## Caveat

The Standard Model group is not semisimple as stated because of the `U(1)`
factor. The current route therefore cannot use a bare
`SU(3) x SU(2) x U(1)` semisimplicity claim. It must either:

- prove that the operative DASHI spine structure group is an `E8`-level
  semisimple extension; or
- provide a separate typed boundary for the reductive `U(1)` factor.

Until that caveat is discharged, the route remains candidate-only.

## Missing Evidence

The route is blocked on:

- `E8SemisimplicityTheoremForSpine`;
- a precise spine structure-group identification theorem;
- a reductive/`U(1)` boundary or embedding theorem;
- `WhiteheadRigidityTheoremForSpine`;
- a cohomology-vanishing theorem at the exact spine algebra;
- `SpineFirstOrderRigidityTheorem`;
- a bridge from rigidity to origin categoricity;
- the existing W8 promotion target,
  `OriginReceiptPromotionExternalReceipt`.

The Agda candidate now also names the theorem imports that would have to
replace the current constructorless tokens:

- `importActualE8SemisimplicityTheorem`;
- `importWhiteheadLemmaForExactSpineAlgebra`;
- `importCohomologyVanishingForExactCoefficientModule`;
- `importRigidityToOriginCategoricityTheorem`.

These are candidate requirements only. No actual semisimplicity, cohomology, or
categoricity module is imported by the route candidate.

## Typed Caveats

The route keeps three caveats typed:

- `u1FactorNotSemisimpleAsStandardModelProduct`;
- `embeddingMustIdentifyOperativeSpineGroup`;
- `reductiveFactorNeedsSeparateBoundary`.

This means the route cannot claim that the Standard Model product directly
supplies semisimplicity. It must either identify an operative E8-level spine
embedding or provide a separate reductive boundary for the `U(1)` factor.

## Non-Claims

- This is not an origin categoricity theorem.
- This is not a Whitehead lemma proof.
- This does not prove semisimplicity of the DASHI spine structure group.
- This does not promote W8.
- This does not construct `OriginReceiptPromotionExternalReceipt`.
- The current minimal-credible shift origin receipt remains `empiricalBlocked`.

## Current Reading

The useful state update is narrow: W8 is no longer only an external-origin
authority request surface. It now also has an explicitly named internal
rigidity route candidate. The route is potentially useful, but every theorem
needed to turn it into evidence is still missing.
