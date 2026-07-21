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