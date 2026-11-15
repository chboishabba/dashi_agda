# Steelman and proof-search: 111₃, signed ternary cube, diamond NV orientations

## Native source-root inventory
- `DASHI.Foundations.AllOnesPadicThresholdBoundary`: proves
  `allOnesPrefix 3 ≡ 13`; the 3-adic extension remains separate.
- `DASHI.Wikimedia.IbrahimZeroToThirteenTernaryCarryNDimFibreSnowballExact`:
  0..13 ternary atlas, with r13 carrying digits 1,1,1 and
  `1 + 3 + 9 = 13`; OEIS A007089 provenance.
- `DASHI.Foundations.BalancedTernaryStageSymmetryExact`:
  `TriadPattern`, `allPositive`, counts and signed balance.
- PR #1238: source NV crystal orientation axes [111] as
  four unoriented direction labels; PR #1262: proves that
  cycling spin-one energy labels does not preserve Sz²=(1,0,1).
- PR #1261: `DiamondNVFourAxisPermutationExact` and new
  `DiamondTernary111AxisBridgeExact`.

## Steelman: the strongest lawful identification
The all-positive balanced triad may be interpreted as vector
(+1,+1,+1) in the integer three-lattice. Restrict the 3³=27
balanced ternary cube to the eight zero-free signed corners
{±1}³, then quotient by global antipodal sign to obtain four
unoriented body diagonals of a cube. The resulting four-element
set is the existing four NV-axis label carrier.

This is not mere numerology: it is equivariant under integral
signed-coordinate permutations W(B3), and hence any subgroup
stabilising an appropriate cubic/diamond lattice. In particular:
- C3 coordinate cycle (x,y,z)↦(y,z,x): order 3; [111] fixed;
- C4 z-rotation (x,y,z)↦(-y,x,z): order 4;
- antipodal quotient commutes with both because -Id is central.

The *radix evaluation* of the three ordinary ternary digits
`111₃` is 13, however, and is **not** invariant under independent
spatial sign changes and permutations if the digits are interpreted
as positional coefficients. Thus the 13 scalar and the [111]
direction are two distinct consumers of a common three-slot
pattern; the vector retains geometric information that the scalar
observer discards.

## Counterexample / obstruction
The 27 ternary triples are not four axes. They stratify by zero
content: 8 corners with 0 zeros; 12 points with 1 zero;
6 points with 2 zeros; 1 origin with 3 zeros. Only the
zero-free eight are mapped by the particular antipodal quotient.

Furthermore, the spatial C3 fixing the [111] direction acts on
**coordinates**, not the three spin-one magnetic sublevels.
As PR #1262 demonstrates, permuting +1→0→−1 is not generally
a symmetry of the NV zero-field splitting Sz². No map between
the two C3 actions is asserted without a Hamiltonian intertwiner.

## Group-theoretic refinement
For full O_h = W(B3), the action on four unoriented body
diagonals has an effective S4 permutation quotient; its kernel
is the central inversion {±I}. For an oriented [111] direction,
the stabiliser has order 48/8=6 (C3v, isomorphic S3).
For an unoriented [111] axis, stabiliser order is 48/4=12,
including operations reversing its direction. Physical NV
centres have distinguishable N and vacancy sites, so the
oriented site stabiliser is the relevant initial local group.

## Further kernel obligations
1. Extend the existing B4 Weyl signed-coordinate action by a
   concrete B3 embedding and formalise its induced action on
   zero-free balanced ternary triples.
2. Prove a quotient-set equivalence (rather than only a
   surjective map with section) to NV axes, with all fibres
   exactly the antipodal pair.
3. Prove induced O_h→S4 homomorphism, surjectivity and
   kernel {±I}; derive orbit/stabiliser and oriented C3v.
4. Transport NV axial spin-one Hamiltonian representations
   through genuine unitary intertwiners; explicitly reject a
   three-label cyclic permutation that fails energy preservation.
5. Test the resulting invariant/anisotropy predictions against
   NV ODMR and crystal-orientation data with experiment-specific
   calibration, rather than promoting algebra into measurement.

## Verification and attribution
The finite corner/axis C3/C4 equivariance was enumerated locally
for all eight corners using independent Python signed triples.
The Agda terms are committed but not typechecked in this runtime.
All textbook crystallographic symmetry, quotient/group action
and NV-centre physical facts are external prior art. DASHI's
novelty claim is restricted to its cross-module typed adapter,
proof-search pipeline and experiments, preserving the source
and historical attribution ledgers.
