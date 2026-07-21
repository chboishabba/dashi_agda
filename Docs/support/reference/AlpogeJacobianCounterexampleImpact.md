# Alpöge Jacobian counterexample: repository impact

## Attribution

The concrete polynomial map checked by this repository was publicly announced
by **Levent Alpöge** on 20 July 2026. His announcement credited **Akhil Mathew**
for asking about the problem and **Fable** for producing the example. DASHI
attributes the public mathematical announcement to Alpöge and makes no claim of
discovery priority.

`DASHI.Provenance.AIAssistedMathematicsProvenance` separates the roles of
question source, prompting agent, generation system, public announcer,
executable verifier, independent verifier, kernel formaliser, and downstream
consequence author. These roles must not be collapsed into a single discovery
label.

## Checked content

The independent executable exact-arithmetic diagnostic
`scripts/check_jacobian_noninjective_example.py` verifies:

1. the displayed map is polynomial in three variables;
2. its Jacobian determinant is identically `-2`;
3. three distinct rational points map to `(-1/4, 0, 0)`.

`Verification.JacobianCounterexampleKernel` now supplies a second, Agda-kernel
lane:

- an exact three-variable polynomial syntax;
- recursive symbolic differentiation;
- an exact `3 x 3` determinant expression;
- rational ring normalization of `det DF = -2`;
- exact rational definitions of all three source points and their common image;
- the generic theorem that a collision of unequal inputs refutes injectivity;
- an explicit `KellerMap3` package;
- a refutation of the dimension-three statement formulated over that package;
- identity-coordinate padding over an arbitrary finite tail.

The Python regression and the Agda proof are deliberately retained as separate
verification paths.

## Mathematical consequence

The checked map is a non-injective polynomial map `C^3 -> C^3` with nonzero
constant Jacobian determinant. It refutes the general Jacobian conjecture in
dimension 3. Appending untouched coordinates transports the counterexample to
every dimension at least 3.

The three-variable construction does **not** settle the separate dimension-2
case. Historical status metadata is source-dated and is not used as a kernel
proof object.

## Evidence-gated promotion

This example is the reference case for the governance sequence

```text
proposal
  -> independent exact executable check
  -> provenance record
  -> kernel polynomial theorem
  -> kernel logical consequence
  -> promoted mathematical status
```

Fail-closed review is an initial staging discipline, not a permanent embargo on
surprising results. `DASHI.Governance.EvidenceGatedTheoremPromotion` requires a
fixed formula, exact regression, provenance, kernel collision proof, kernel
Jacobian proof, and kernel logical consequence before promotion.

## Local versus global inversion

The counterexample separates several properties that must never be silently
identified:

```text
nonzero local Jacobian
!= properness at infinity
!= global injectivity
!= generic fibre degree
!= monodromy classification
!= existence of one global inverse
```

`DASHI.Topology.LocalGlobalMapDiagnostics` checks everywhere local
nonsingularity and the displayed three-point fibre while leaving properness,
generic degree, monodromy, and boundary escape behind explicit authorities.

`DASHI.Algebra.LocalInverseVsGlobalInverse` distinguishes neighbourhood-local
inverse charts from the repository's two-sided `Invertible` record. The exact
collision kernel-refutes any global inverse. Applying the complex inverse
function theorem is separately represented by an authority rather than
manufactured from the name “Jacobian.”

## Global ambiguity beside `MereViol`

`MereViol` remains a local overlap conflict: two local sections assert
incompatible exclusive values and therefore cannot carry a compatibility/glue
witness.

`GlobalAmbiguity` is different:

```text
local sections are valid
+ compatible families glue
+ each fixed compatible family has a unique glue
+ a later observation maps distinct global sections to one visible value
```

`DASHI.Sheaf.GlobalAmbiguityBoundary` contains two exact instances:

1. two different temporal global sections with the same overlap-only
   observation;
2. the two distinct polynomial source points with the same image under `F`.

This does not contradict sheaf uniqueness. Sheaf uniqueness says that one fixed
compatible local family has at most one global glue. It does not say that every
observation of all global sections is injective.

The failure taxonomy is therefore:

- `MereViol`: incompatible local data;
- gluing failure: no global section for a local family;
- non-unique gluing: multiple global sections for the same compatible family;
- global ambiguity: different valid global states share a coarser observation.

## Computational reductionism boundary

Global ambiguity captures a central *representational reductionist* move, but
not computation in general.

The problematic promotion is:

```text
selected computable observation
  => complete, context-free, globally lossless identity code
```

Formally, this is the assumption that the observation map is injective.
`DASHI.Philosophy.ComputationalReductionismBoundary` proves that a
`GlobalAmbiguity` witness refutes that observational-completeness claim and any
larger closure record carrying it.

This does **not** imply that all computation is reductionist or all computable
models are noninjective. Injective encodings, context-bearing models, residual
channels, relational representations, and fibre/sheet-aware computations remain
available. The distinction is:

```text
computation != reductionism
reductionism = treating one selected projection as exhaustive of the world
```

## Exact triadic sheet label

The displayed fibre has source points whose first coordinates are `-1`, `0`,
and `+1`. `DASHI.Foundations.JacobianThreeSheetTriadicBridge` therefore permits
a balanced-ternary sheet label after the fibre has been proved.

The direction is intentionally one-way:

```text
exact three-point fibre -> optional {-1,0,+1} labelling
```

The labels do not prove the fibre's existence, and the exceptional three-point
fibre does not by itself establish the generic fibre degree.

## MDL and source identity

`DASHI.MDL.SheetAwareAmbiguityPenalty` separates:

- model description cost;
- reconstruction residual cost;
- unresolved sheet/source-identity cost.

Its finite worked comparison shows that a visibly simpler one-sheet model need
not be preferred when it destroys source identity. The numerical costs are a
reference example, not a universal coding scale.

## Effect on existing DASHI results

The result changes content only when it uses the invalid global implication

```text
constant nonzero Jacobian => polynomial automorphism
```

without extra hypotheses in dimension at least 3.

No pre-existing DASHI theorem module was found with that four-part dependency.
The inverse-related modules inspected are unaffected:

- `DASHI.Core.OperatorTypes.Invertible` carries an explicit inverse and both
  round-trip laws;
- `DASHI.Algebra.ProjectionVsInvertible` assumes that evidence;
- `DASHI.Culture.InverseBidirectionalCultureOperators` proves its concrete
  round trips directly;
- `DASHI.Biology.BodyMemoryCompiledInverseBridge` is chart-local and
  candidate-only, with stronger authority blocked.

Unrelated physics, analysis, biology, runtime, empirical, and cultural lanes do
not change merely because they mention an inverse, determinant, or Jacobian.

## Ongoing review guard

A future module should be flagged only when all four conditions hold:

1. it concerns a polynomial self-map of affine space;
2. the ambient dimension is at least 3 or unrestricted;
3. its only global hypothesis is a nonzero constant Jacobian determinant;
4. it concludes injectivity, surjectivity, polynomial inverse, or automorphism.

Future modules should distinguish:

- `JacobianConjectureDimension2` — separate and not settled here;
- dimension-three and padded dimension-at-least-three refutations;
- restricted invertibility theorems with their exact additional hypotheses.

## Remaining global analyses

The kernel theorem does not automatically supply:

- properness or failure-of-properness classification;
- generic fibre degree;
- monodromy;
- topology at infinity;
- a full complex-analytic formalisation of the inverse function theorem;
- a classification of larger counterexample families.

Those are downstream mathematical projects rather than prerequisites for the
explicit counterexample.
