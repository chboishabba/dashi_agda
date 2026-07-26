# Marx differential algebra in DASHI

## Implemented spine

The formal sequence is now explicit:

```text
original function
  -> finite transport
  -> preliminary derived function
  -> factorisation receipt
  -> lawful diagonal collapse
  -> final derived function
```

For a selected algebra `A`, a factorisation receipt contains a two-point preliminary function `F` and the equation

```text
f(x1) - f(x) = (x1 - x) * F(x,x1).
```

The Marx derivative is then definitionally

```text
D_M f(x) = F(x,x).
```

No quotient is evaluated on the diagonal. `RawDiagonalQuotient` requires a proof that `x - x` is nonzero, and `rawDiagonalQuotientImpossible` contradicts that requirement using `subSelf`.

## Exact algebraic results

`MarxDifferentialCore` constructs and proves:

- constant factorisation and `D_M(c)=0`;
- identity factorisation and `D_M(x)=1`;
- closure under addition;
- closure under multiplication;
- the sum rule;
- the product rule;
- composition factorisation from nested finite transports;
- the chain rule;
- quotient factorisation as multiplication by a separately receipted reciprocal.

The quotient's conventional denominator-squared normal form remains parameterised by `QuotientRuleNormalisation`. This is intentional: a reciprocal operation alone does not select all subtraction, commutativity, and denominator-normalisation laws needed by that printed formula.

## Polynomial regime

`MarxPolynomialDifferential` builds powers recursively from the identity and product constructors. It proves the exact recursive power derivative and defines a polynomial syntax with constructed factorisation receipts for constants, variables, sums, and products.

The conventional display

```text
D_M(x^n) = n * x^(n-1)
```

is exported through `PowerRuleNormalisation`. The recursive derivative is already constructed; the remaining field is precisely the algebra-specific normalisation from repeated sums/products to a selected natural-scalar action. The terminal regression inhabits this interface without presenting the one-point model as ordinary analysis.

## Ordinary derivative bridge

`MarxOrdinaryDerivativeBridge` adds:

- a remainder-based derivative expansion;
- a diagonal-continuity receipt for the preliminary function;
- the theorem surface

```text
Marx factorisation
+ continuous diagonal
+ ordinary remainder derivative
-> D_M f(x) = D f(x).
```

The repository's constructive-real spine currently has Cauchy completion and transcendental constructions but no selected normed derivative topology. Consequently, the compatibility proof is represented by the explicit `MarxOrdinaryCompatibilityAuthority` boundary rather than fabricated from insufficient structure.

A concrete `ConstructiveRealDerivativeSeam` is the next analytic inhabitant: it must bind the selected constructive real to a norm/topology, prove diagonal continuity, and discharge the remainder argument.

## Higher calculus

`MarxHigherCalculus` supplies typed surfaces for:

- iterated derivatives;
- derivative-closed function families;
- higher-derivative towers;
- Taylor coefficients `D^n f(a)/n!`;
- directional derivatives;
- Frechet derivatives;
- directional/Frechet compatibility;
- Jacobians;
- differential forms and `d^2=0`;
- integration and fundamental-theorem bridges.

These interfaces do not claim that the current constructive-real carrier already inhabits every analytic law.

## Social recursion differential

`TraumaExploitationDifferential` differentiates the heterogeneous recursion

```text
HistoricalState
  -> SufferingField
  -> ExploitationProtocol
  -> Institution
  -> HistoricalState.
```

The exact local propagation operator is the typed chain

```text
dReproduce
  o dInstitutionalise
  o dExploitationExtraction
  o dTraumaProduction.
```

`DifferentialAttribution` keeps distinct:

- where suffering enters;
- where it is converted into an exploitation protocol;
- where it becomes institutionally scalable;
- where it is reproduced or externalised.

A large local differential gain does not produce normative authority.

## Files

- `DASHI/Analysis/MarxDifferentialCore.agda`
- `DASHI/Analysis/MarxPolynomialDifferential.agda`
- `DASHI/Analysis/MarxOrdinaryDerivativeBridge.agda`
- `DASHI/Analysis/MarxHigherCalculus.agda`
- `DASHI/Analysis/MarxDifferentialRegression.agda`
- `DASHI/Analysis/MarxDifferentialBundle.agda`
- `DASHI/Governance/TraumaExploitationDifferential.agda`

## Remaining substantive work

1. Instantiate `MarxAlgebra` on the repository's nondegenerate constructive real.
2. Prove the algebra-specific power normalisation rather than merely providing its interface.
3. Construct a reciprocal factorisation and denominator-squared quotient normalisation.
4. Add a norm/topology and prove the ordinary-derivative compatibility authority.
5. Inhabit Frechet, Jacobian, forms, integration, and fundamental-theorem structures on that same carrier.
6. Supply evidence-bound empirical social-system instances; the generic differential architecture alone proves no historical or geopolitical claim.
