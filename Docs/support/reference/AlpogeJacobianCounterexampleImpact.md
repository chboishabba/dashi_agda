# Alpöge Jacobian counterexample: repository impact

## Attribution

The concrete polynomial map checked by this repository was publicly announced
by **Levent Alpöge** on 20 July 2026. His announcement credited **Akhil Mathew**
for asking about the problem and **Fable** for producing the example. DASHI
attributes the public mathematical announcement to Alpöge and makes no claim of
discovery priority.

## Checked content

The executable exact-arithmetic diagnostic
`scripts/check_jacobian_noninjective_example.py` verifies:

1. the displayed map is polynomial in three variables;
2. its Jacobian determinant is identically `-2`;
3. three distinct rational points map to `(-1/4, 0, 0)`.

`Verification/JacobianNoninjectiveRegression.agda` now kernel-checks the general
logical step that an unequal pair with equal image refutes injectivity. The
large polynomial expansion is still performed by the exact executable checker,
not by an Agda polynomial normaliser.

## Mathematical consequence

Taken together, the checks give a non-injective polynomial map
`C^3 -> C^3` with nonzero constant Jacobian determinant. This refutes the
general Jacobian conjecture in dimension 3. Appending untouched coordinates
gives the corresponding consequence in every dimension at least 3.

This does **not** settle the dimension-2 case.

## Effect on DASHI

The result changes the status of content that treats the unrestricted Jacobian
conjecture in dimensions at least 3 as an open target, plausible global
principle, or safe inverse-function heuristic. Such content must instead use
one of the following narrower statements:

- local invertibility from a nonzero Jacobian determinant;
- a dimension-2-specific conjectural statement;
- a globally injective/proper/birational hypothesis stated independently;
- a restricted polynomial class for which global invertibility is separately
  proved.

The counterexample does not automatically alter unrelated DASHI results in
analysis, Navier--Stokes, Yang--Mills, topology, arithmetic, biology, empirical
work, or runtime systems. It matters only where those lanes rely on the invalid
global implication

`constant nonzero Jacobian => polynomial automorphism`

without extra hypotheses.

## Dependency audit

The current authoritative import surface and the most plausible inverse-labelled
consumers were reviewed for dependence on that implication.

### Result

No existing theorem module was found that derives global invertibility of a
polynomial map from a nonzero constant Jacobian determinant. Accordingly, no
pre-existing mathematical theorem needs to be weakened by this change.

The inverse-related modules inspected use materially different hypotheses:

- `DASHI.Core.OperatorTypes.Invertible` stores an inverse function together with
  explicit left- and right-inverse laws. Invertibility is evidence carried by
  the record, not inferred from a derivative or determinant.
- `DASHI.Algebra.ProjectionVsInvertible` assumes that explicit `Invertible`
  witness and proves that an idempotent invertible operator is the identity.
- `DASHI.Culture.InverseBidirectionalCultureOperators` defines concrete inverse
  operations and checks the relevant round-trip equalities directly.
- `DASHI.Biology.BodyMemoryCompiledInverseBridge` is a candidate-only semantic
  bridge whose “inverse” terminology is chart-local and explicitly
  non-authoritative; it does not state a polynomial global-inverse theorem.

The only directly affected repository surfaces are therefore the newly added
Jacobian diagnostic, its verification receipt, and documentation describing the
status of the conjecture.

### Review classification

- **Direct invalid dependency:** none found.
- **Inverse records with explicit two-sided laws:** unaffected.
- **Concrete involutions or round-trip witnesses:** unaffected.
- **Chart-local, metaphorical, or candidate-only inverse language:** unaffected,
  provided it is not later promoted into a polynomial global-invertibility
  theorem.
- **Local inverse-function uses:** unaffected when they conclude only local
  invertibility.
- **Future dimension-2 statements:** must be dimension-indexed and remain
  conjectural unless separately proved.

### Ongoing guard

Future review should flag a module when all of the following are present:

1. the carrier is a polynomial self-map of affine space;
2. the ambient dimension is at least 3 or left unrestricted;
3. the only global hypothesis is a nonzero constant Jacobian determinant;
4. the conclusion supplies injectivity, surjectivity, a polynomial inverse, or
   an automorphism.

A module is not affected merely because it contains the words `inverse`,
`invertible`, `Jacobian`, or `determinant`; the proof dependency must match the
four-part pattern above.

## Audit rule

Future modules should not use `JacobianConjecture` as an undifferentiated name.
They should distinguish at least:

- `JacobianConjectureDimension2` -- unresolved;
- `GeneralJacobianConjectureDimensionAtLeast3` -- refuted by the Alpöge example;
- restricted invertibility theorems with their exact additional hypotheses.

The example should also remain a provenance lesson: computational discovery,
public announcement, exact executable verification, kernel-checked logical
consequence, and broader mathematical interpretation are separate layers and
should be attributed and typed separately.
