# Tekum balanced-ternary formalisation

This tranche formalises Laslo Hunhold's Tekum representation together with the binary-coded ternary signed-digit FPGA result boundary of Thomas Schlögl and Dietmar Fey, while reusing the repository's pre-existing floating-point, triadic/p-adic, ternary-machine, binary/ternary storage and ABI owners.

## Native Tekum spine

The implementation reuses `DASHI.Algebra.Trit`; it does not introduce a Tekum-specific trit. `BalancedTernaryIntegerExact` supplies the positional radix-three ledger and proves digitwise involution swaps positive and negative weight.

`TekumAnchorArithmeticExact` states Hunhold's source definition

    anc_n(t) = |t| - 11...1

over a selectable fixed-width balanced arithmetic backend and proves `anc_n(-t)=anc_n(t)` from the backend modulus law.

`TekumRegimeExponentExact` encodes the fifteen anchored regime states (r=-7,ldots,7), the source exponent-count rule (c=max(0,|r|-2)), and the bias magnitudes (0,1,2,4,10,28,82,244). `TekumSpecialValuesExact` classifies the all-negative, all-zero and all-positive words as NaR, zero and infinity.

## Existing floating-point spine

`BinaryFloatingPoint` already separates radix from scale policy and assigns structural roles to sign, exponent and fraction:

    sign     -> orientation
    exponent -> scale transport
    fraction -> local refinement

`RadixScaledExactFormat` factors only that reusable structure. BF16 becomes the fixed-width radix-2 instance and Tekum becomes the radix-3 instance.

`TekumFloatingPointStructuralBridgeExact` makes the tapered distinction explicit. For an (n)-trit Tekum, the three-trit regime is fixed while the remaining (n-3) payload is divided between exponent and fraction according to the regime. At width eight the central regime gives all five payload trits to the fraction, whereas the outer (r=+7) regime gives all five to the exponent.

Thus the shared structure is exact, while the allocation policy differs:

    BF16  : fixed exponent width + fixed fraction width
    Tekum : regime-dependent exponent width + complementary fraction width

## Existing triadic / p-adic spine

`TekumTriadicPAdicKernelBridgeExact` proves an exact bidirectional carrier weld

    Data.Vec Trit n  <->  TriadicPAdicCodec.Kernel n

rather than creating another ternary word type.

The two-trit Tekum precision projection commutes definitionally with the corresponding projection on the canonical triadic kernel. Nested projection is also paid:

    project2 (project2 x) = project4 x

This gives the representation-level naturality behind staged Tekum precision reduction. The bridge explicitly does **not** claim that a Tekum real is therefore a literal p-adic valuation; p-adic interpretation remains a separate semantic layer.

## Existing ternary computer spine

`TekumTernaryStoredProgramExecutionExact` gives a concrete machine integration rather than only a hardware-interface record.

Each of the fifteen Tekum regimes is assigned a bounded index (0,ldots,14), passed through the existing `FixedNineBitFramed27WordStorageExact` ternary-27 storage fibre, and decoded back exactly. The decoded memory initializes the existing `TinyRadixNeutralRegisterMachineExact`.

For every regime, the ternary-storage machine state equals the native-memory machine state before execution, hence their final states are equal. The concrete outer positive regime executes the echo program and produces:

    output = [14]

This is a representation theorem, not a claim that the radix-neutral machine has a physical ternary ALU.

## SSP / FRACTRAN attachment

The bridge is constructive and orthogonal to the native numeric semantics.

1. `Trit <-> SSPTrit` reuses the existing exact bidirectional codec.
2. A positioned Tekum digit projects to the existing signed SSP/FRACTRAN orientation.
3. Its ternary position is retained as a dependent residual.
4. Coarse orientation plus residual reopens the exact positioned Tekum digit.
5. Position (k) determines the radix weight (3^k).
6. The executable compiler maps (+1) to (3^k) prime-introduction instructions, (-1) to (3^k) inverse-prime instructions and (0) to no arithmetic instruction.

`TekumFieldRoleSSPAtlasExact` supplies both a single radix-three lane and an explicit separated regime/exponent/fraction atlas. Lane selection is representation metadata, not an assertion that Tekum numerical values are Monster/Ogg prime products.

## Existing ABI and FPGA boundaries

`TekumTriadicABIBackendBoundaryExact` reuses both the existing triadic three-trit byte reference and `TriadicPAdicCodec.Pack5Contract`. The two-bit-per-trit codec remains exact, while Rust u8, SWAR runtime and FPGA netlist claims stay unpaid unless separately implemented.

`SchloeglFeyFPGASourceBoundaryExact` therefore remains an attributed empirical receipt for the reported UltraScale LUT and carry-chain results rather than a gate-level proof.

The repository keeps three engineering coordinates distinct:

    storage density
    transition/locality dilation
    adder critical-path / physical timing

## Formal-property targets

`TekumNegationExact` pays the anchor-invariance part of Hunhold Proposition 3. `TekumUniquenessExact` and `TekumMonotonicityExact` expose exact contracts for Propositions 2 and 4. `TekumTruncationRoundingExact` owns structural anchor truncation and `TekumPrecisionCompositionExact` proves multi-stage truncation composition.

The remaining mathematical frontier is still the concrete fixed-width balanced integer inverse/arithmetic backend and the ordered exact-rational instantiations needed for injectivity, monotonicity and nearest-value rounding.

## Sources

- Laslo Hunhold, *Tekum: Balanced Ternary Tapered Precision Real Arithmetic*, arXiv:2512.10964 (2025).
- Thomas Schlögl and Dietmar Fey, *Ternary Signed Digit Addition on Field Programmable Gate Arrays*, ARCS 2025 / LNCS 15839 (2026), DOI `10.1007/978-3-032-03281-2_3`.
