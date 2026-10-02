# Tekum balanced-ternary formalisation

This tranche formalises Laslo Hunhold's Tekum representation together with the binary-coded ternary signed-digit FPGA result boundary of Thomas Schlögl and Dietmar Fey.

## Native spine

The implementation reuses DASHI.Algebra.Trit; it does not introduce a Tekum-specific trit. BalancedTernaryIntegerExact supplies the positional radix-three ledger and proves digitwise involution swaps positive and negative weight.

TekumAnchorArithmeticExact states Hunhold's source definition anc_n(t)=|t|-11...1 over a selectable fixed-width balanced arithmetic backend and proves anc_n(-t)=anc_n(t) from the backend modulus law.

TekumRegimeExponentExact encodes the actual fifteen anchored regime states r=-7,...,7, the source exponent-count rule c=max(0,|r|-2), and the bias magnitudes 0,1,2,4,10,28,82,244. TekumSpecialValuesExact classifies the all-negative, all-zero, and all-positive words as NaR, zero, and infinity.

## Formal property owners

TekumNegationExact pays the anchor-invariance part of Hunhold Proposition 3. TekumUniquenessExact and TekumMonotonicityExact expose the exact contracts needed to instantiate Propositions 2 and 4 on a concrete ordered rational/real backend. TekumTruncationRoundingExact owns the structural anchor truncation used by Proposition 5, and TekumPrecisionCompositionExact proves repeated two-trit truncation equals direct four-trit truncation.

## SSP / FRACTRAN attachment

The bridge is constructive, not metaphorical.

1. Trit and SSPTrit are reused through the existing exact bidirectional codec.
2. A positioned Tekum digit projects to the existing signed SSP/FRACTRAN orientation.
3. Its ternary position is retained as a dependent residual.
4. Coarse orientation plus residual reopens the exact positioned Tekum digit.
5. Position k determines the radix weight 3^k.
6. The executable compiler maps +1 to 3^k prime-introduction instructions, -1 to 3^k inverse-prime instructions, and 0 to no arithmetic instruction.

TekumFieldRoleSSPAtlasExact then shows two concrete field semantics. canonicalRadixThreeAtlas routes regime, exponent, and fraction through SSP prime 3. separatedRoleAtlas routes them through primes 3, 5, and 7 respectively. The lane choice is explicit representation metadata and does not assert that the Tekum real value is numerically equal to a Monster/Ogg prime product.

## Hardware boundary

VerifiedFiniteTritCoder already supplies the binary-coded ternary map -1->00, 0->01, +1->10 with 11 reserved. SchloeglFeyFPGASourceBoundaryExact records the reported UltraScale FPGA results as attributed empirical evidence rather than kernel-derived circuit timing.

The repository keeps storage density, local transition dilation, and adder critical-path/timing separate. The existing nine-trit codec gives a 15-bit lossless embedding with primitive-transition dilation at most two, while the naive fixed two-bit-per-trit view uses 18 bits.

## Sources

- Laslo Hunhold, Tekum: Balanced Ternary Tapered Precision Real Arithmetic, arXiv:2512.10964 (2025).
- Thomas Schloegl and Dietmar Fey, Ternary Signed Digit Addition on Field Programmable Gate Arrays, ARCS 2025 / LNCS 15839 (2026), DOI 10.1007/978-3-032-03281-2_3.

## Current exact boundary

Paid now: canonical trit reuse, positional signed-radix ledger, source anchor interface, negation-invariant anchor compiler, 15-state regime codec, exponent-count rule, bias table, special-value classifier, symbolic Tekum semantic carrier, binary-code roundtrip, SSPTrit roundtrip, positioned dependent reopening, weighted FRACTRAN compiler, field-role SSP atlas, and structural multi-step truncation composition.

Still theorem inputs: the full concrete int_n inverse/fixed-width Tekum arithmetic backend; the ordered exact-rational/real instantiation of source injectivity and monotonicity; the nearest-value proof for truncation over that same semantic carrier; and a gate-level/netlist proof of the Schlögl-Fey timing/resource implementation.