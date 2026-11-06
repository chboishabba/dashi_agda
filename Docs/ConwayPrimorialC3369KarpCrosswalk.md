# Conway / primorial / C3-369 / Karp-21 crosswalk

## Source implementations

- `DASHI.Foundations.ConwayChainedArrowFiniteBridgeExact`: rank-indexed three-term chains, finite four-term last-2/3 functional iteration, factorial iteration.
- `DASHI.Foundations.ConwayPrime369ComplexityBridgeExact`: intensional growth-code syntax, prime-digit evaluator, explicit 3/6/9 factor-address witness, C3^3 numeric comparisons and representation-cost boundary.
- `DASHI.Foundations.PrimorialFactorAddressConcrete`: four-prime mixed-radix addressing and multiplicative prime-exponent product.
- `DASHI.Foundations.WetteArithmeticRepresentationExact`: Godel-number reconstruction from a factor vector.
- `DASHI.Mathematics.Complexity.PolynomialReductionExact`: languages, extensional reductions and polynomial cost-model obligations.
- `DASHI.Mathematics.Complexity.CookLevinPolynomialSizeExact`: polynomial grid, variable and repeated fixed-template clause accounting.
- `DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact`: canonical bounded cell-to-bits representation.
- `DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact`: SATNotInP iff P!=NP under established-background parameters.
- `DASHI.Core.C3EfficientReopeningExampleExact`: concrete three-point recoverable quotient and constant-cost witness.
- `DASHI.Biology.Physical.C3CubeFourier27Exact`: C3^3 finite carrier and Fourier skeleton.

## The conceptual commuting diagram, with honest interfaces

    Conway symbolic syntax ---> evaluated natural number
             |                         |
       syntax-length              binary numeral
             |                         |
       Karp source word            Karp target word
             \____ genuine algorithm, cost and iff proof ____/

A Conway expression can describe an enormous natural number with relatively
few constructors. That distinction is a succinctness issue, not an NP-hardness
or lower-bound theorem. A polynomial-time many-one reduction must output its
chosen target *word* within its paid time and space bound. Symbolic target
words are permitted only when target-language semantics explicitly interpret
them and the verifier's clock is proved.

A prime factor-address has at least three possible types that must not
be conflated: the integer `n` encoded, the exponent vector describing `n`,
and the numerically evaluated product of primes. The existing repository
shows `primorialDecode4` and `primeExponentProduct4` are distinct maps.
For example, `(0,0,4,0)` decodes to 24 but maps to 625 as a factor
product. Neither map is a Conway chain evaluator.

The new witness `digits369 = (3,6,9,0)` illustrates that distinction:
`primorialDecode4 digits369 = 69`, whereas the multiplicative image is
`2^3 * 3^6 * 5^9`. The phrase '369' here denotes an exponent
coordinate selection, not a base-10 numeral and not a C3 group action.

C3^3 has 3*3*3 = 27 points. The height-two triadic tower satisfies
3^^2=3^3=27. These are equal *numbers*, but the first is a product
space and the second arises from a function-space recurrence.
Exhibiting an actual bijection, equivariance and costed codec is a
separate obligation.

## Karp-21 acceptance gates

K01: full arbitrary positive Conway-chain syntax and terminating evaluator,
plus agreement with the special-case closed witnesses.

K02: a prefix-free, bit-level codec for symbolic chains and factor-exponent
vectors; prove encode/decode roundtrip and bounds on emitted word length.

K03: formalize a *selected* reduction between genuine source and target
languages, with both satisfaction directions, costed compilation and
verified decode. Do not silently use integer evaluation as a polynomial
compiler for arbitrary inputs.

K04: show that the selected C3^3 27-point carrier maps to the intended
three-trit/Bits representation; distinguish numerical cardinality from
a group-action-preserving transport.

K05: reuse the existing `PolynomialReductionExact` and Cook-Levin
cost and soundness contracts for the selected instance, including the
actual machine clock. The P != NP core remains `SATNotInP`; the current
bridges furnish no lower bound.

K06: connect the intended Karp-21 reduction edge(s) to the selected
canonical Cell/Bits words and check the compiled CNF instance, rather
than substituting a succinct arithmetic descriptor for a SAT witness.

K07: exact-head `parallel_checker` acceptance and transitive trust audit.
No checker was executed in this change.

## Non-promotions

Factorial iteration, multi-factorials, Conway chains, primorial mixed-radix
addresses, Wette/Godel scalarization, and C3^3 group carriers are distinct
operations and objects. Distinguishing them is essential to obtaining
sound, reusable complexity theorems.
