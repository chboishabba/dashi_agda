# Tekum balanced-ternary formalisation

This tranche formalises Laslo Hunhold's Tekum representation together with the binary-coded ternary signed-digit FPGA result boundary of Thomas Schlögl and Dietmar Fey, while reusing the repository's existing balanced-ternary, floating-point, triadic/p-adic, ternary-machine, binary/ternary storage and ABI owners.

## Native carrier and integer frontier

The implementation reuses `DASHI.Algebra.Trit`; it does not introduce a Tekum-specific trit.

`BalancedTernaryIntegerExact` supplies the least-significant-trit-first positional radix-three signed-weight evaluator and proves digitwise involution swaps positive and negative weight.

`BalancedTernaryA003462BridgeExact` now reuses the repository's older A003462 owner for the canonical maximum-magnitude sequence

    1, 4, 13, ...

rather than creating a second bound sequence. The three-positive-trit evaluator is welded directly to the existing magnitude 13 receipt.

`BalancedTernaryFiniteCarrierExact` pays the finite carrier side exactly:

    Trit ≃ Fin 3
    Trit^n ≃ (Fin 3)^n

and reuses the repository's complete duplicate-free finite-product enumerator together with its exact cardinality theorem

    #(Fin 3)^n = 3^n.

This is important but deliberately does not pretend that cardinality alone proves injectivity of the positional integer evaluator. The remaining integer theorem is specifically that the signed radix-three positional map is the bijection onto the centered interval of the same cardinality.

## Tekum anchor and regime

`TekumAnchorArithmeticExact` states Hunhold's source definition

    anc_n(t) = |t| - 11...1

over a selectable fixed-width balanced arithmetic backend and proves `anc_n(-t)=anc_n(t)` from the backend modulus law.

`TekumRegimeExponentExact` encodes the fifteen anchored regime states (r=-7,ldots,7), the source exponent-count rule (c=max(0,|r|-2)), and the bias magnitudes (0,1,2,4,10,28,82,244). `TekumSpecialValuesExact` classifies the all-negative, all-zero and all-positive words as NaR, zero and infinity.

## Exact ordinary semantics

`TekumFiniteSemanticsExact` retains the source-level ordinary/special distinction.

`TekumExactTriadicSemanticsExact` now gives the radix-three analogue of the repository's existing `BinaryFloatingPoint.ExactDyadic`. An ordinary Tekum value

    s (1 + F / 3^p) 3^e

is represented exactly as

    s (3^p + F) 3^(e-p)

using the existing `BinaryFloatingPoint.SignedScale` owner.

The same file now promotes that symbolic object to the repository's canonical `Data.Rational.Base.ℚ` with `normalize`. Thus ordinary finite Tekum semantics no longer require machine Float or an ambient real completion.

NaR and infinity remain outside `ℚ`; they are not silently coerced into finite rationals.

## Existing floating-point spine

`BinaryFloatingPoint` already separates radix from scale policy and assigns structural roles to sign, exponent and fraction:

    sign     -> orientation
    exponent -> scale transport
    fraction -> local refinement

`RadixScaledExactFormat` factors only that reusable structure. BF16 is the fixed-width radix-2 instance and Tekum is the radix-3 tapered instance.

`TekumFloatingPointStructuralBridgeExact` proves the coordinate-role identifications definitionally. At width eight the central regime gives all five payload trits to the fraction, while the outer (r=+7) regime gives all five to the exponent.

## Existing triadic / p-adic spine

`TekumTriadicPAdicKernelBridgeExact` proves

    Data.Vec Trit n  <->  TriadicPAdicCodec.Kernel n

with both roundtrips.

`TriadicPAdicCylinderExact` instantiates the repository's existing `CylinderSystem`: low-to-high residual streams project to low-order prefixes and refinement forgets the newest high-order digit.

This reveals the exact orientation mismatch:

    Tekum precision truncation : drops low-order anchor trits
    canonical 3-adic cylinder : retains low-order prefix.

`TekumPadicOrientationBoundaryExact` proves with a concrete counterexample that the two maps are not literally identical.

`TekumPadicDualChartExact` now supplies the exact involutive reversal chart

    D = reverse

and defines the conjugate precision operation

    D ∘ truncate₂ ∘ D.

Agda proves

    D (truncate₂ x) = dualPrecision₂ (D x)

and the two-step precision composition theorem survives this conjugation. This pays the finite orientation conversion. It still does not promote a Tekum real to a p-adic valuation, and the final theorem identifying the conjugated operation with the executable cylinder refinement remains a distinct bridge target.

## Existing ternary computer spine

`TekumTernaryStoredProgramExecutionExact` maps all fifteen regime codes through `FixedNineBitFramed27WordStorageExact`, reconstructs the same `TinyRadixNeutralRegisterMachine` memory, and therefore proves the same final machine state after execution.

The outer positive regime concretely echoes

    [14].

This is executable representation transport through the existing ternary computer substrate, not a physical ternary-ALU timing claim.

## SSP / FRACTRAN attachment

The SSP/FRACTRAN lane remains constructive and orthogonal to native numeric semantics:

1. exact `Trit <-> SSPTrit`;
2. positioned digit -> signed orientation;
3. dependent residual retains position;
4. exact reopening;
5. position (k) supplies radix weight (3^k);
6. executable repeated prime/inverse-prime presentation.

Lane selection remains explicit representation metadata rather than a claim of numerical identity with Monster/Ogg prime products.

## ABI and FPGA boundaries

`TekumTriadicABIBackendBoundaryExact` reuses the existing three-trit byte reference and `TriadicPAdicCodec.Pack5Contract`.

`SchloeglFeyFPGASourceBoundaryExact` remains an attributed empirical receipt. Rust u8 bindings, SWAR runtime kernels and a gate-level FPGA netlist are separate implementation obligations.

## Remaining mathematical frontier

The large representation architecture is now mostly paid. The remaining hard mathematical chain is narrower:

1. prove the positional balanced-ternary evaluator is injective / reconstructive onto the centered A003462 interval;
2. instantiate the full fixed-width wrapping arithmetic and inverse required by the source `int_n`;
3. use the now-concrete `ℚ) decoder to prove Hunhold Proposition 2 injectivity;
4. prove Proposition 4 ordered-code monotonicity on the same rational carrier;
5. prove Proposition 5 nearest-value truncation, not merely structural composition;
6. identify the reversal-conjugated finite projection with the executable p-adic cylinder refinement if that naturality transport is desired;
7. reconstruct a specific Schlögl-Fey digit network before claiming a kernel-checked width-independent circuit-depth bound.

## Sources

- Laslo Hunhold, *Tekum: Balanced Ternary Tapered Precision Real Arithmetic*, arXiv:2512.10964 (2025).
- Thomas Schlögl and Dietmar Fey, *Ternary Signed Digit Addition on Field Programmable Gate Arrays*, ARCS 2025 / LNCS 15839 (2026), DOI `10.1007/978-3-032-03281-2_3`.
