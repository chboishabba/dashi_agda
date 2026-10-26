# Nine-site alternating-lobe braid: exact finite max-cut

## Source and scope
User-specified moving 1 in a 3×3 sheet, rows and columns zero-based; derived continuous embedding uses **linear interpolation in the plane** and braid-time as a third coordinate. The user supplied the first nine states and stipulated that later excursions alternate right/left. The 12-cycle and its interpolation are an explicit modelling choice, not an assertion of geometric inevitability.

Positions at t=0..11:
```text
(0,0) (0,1) (1,1) (2,1) (2,2) (1,2)
(0,2) (0,1) (1,1) (2,1) (2,0) (1,0)
```
and p(t+12)=p(t). Define A(t)=p(t), B(t)=p(t+4), C(t)=p(t+8) (indices mod 12). On intervals [k,k+1] interpolate each trajectory linearly and lift using time as the third coordinate.

## Verified finite receipts
A Python exact-rational executable accompanying this note evaluates:
1. 3 distinct sites at all twelve samples.
2. No collision between any two concurrent linear segments at equal t (solving affine relative-coordinate equations over rationals).
3. Equivariance: (A,B,C)(t+4)=(B,C,A)(t).
4. Winding numbers of each ordered planar difference curve around 0: all zero.
5. Projection to a generic line x=column+row/7, depth=row-column/11 gives the braid word
   `sigma_1^{-1} sigma_2 sigma_1^{-1} sigma_2 sigma_1^{-1} sigma_2`.
   Opposite diagram orientation reverses signs / conjugates accordingly.

Its **standard closure** is Borromean rings: pairwise unlinking but nontrivial triple linking. The closure claim uses the standard known 3-braid identification, not a separately kernel-checked topological equivalence here. Milnor's triple invariant of this closure is ±1.

## Keep separate
- `Z3 × Z3` is a nine-address carrier, *not* the 3-sphere.
- `t -> t+4` on this 12-cycle has order 3; it need not be geometrically equivalent to an SU(2) action.
- Hopf map: `h(z,w)=(2Re(z conjugate(w)),2Im(z conjugate(w)),|z|²-|w|²)`, with `|z|²+|w|²=1`. Distinct Hopf fibres link pairwise ±1, unlike our Borromean closure.
- The `SU(2) -> SO(3)` preimage of a specified order-3 rotation subgroup is order 6. This is not proof of a 9-dimensional physical space.
- A toroidal / Villarceau embedding needs an explicit map, proof of fibres and linking, not a visual analogy.
- Projection crossing word depends on interpolation and chosen regular braid projection; endpoints alone do not determine the word.

## Proposed typed integration
- `NineSite` = ordered pair of ternary coordinates, and `time12` cyclic index.
- `AlternatingOrbit` = lookup of twelve positions.
- `ThreePhaseConfiguration t` = positions at offsets 0,4,8.
- `DistinctAt t`, `ContinuousCollisionFree`, `Shift4Equivariant`.
- `RegularBraidProjection` supplies crossing time, strand ordering and over/under sign.
- `BraidWord`, `BraidClosure`, `BorromeanClosureWitness` must stay separate types.
- `HopfCandidate` needs a map to `S3`, Hopf base-map compatibility and actual linking witnesses, not a coercion from finite orbit.

## Local reproduction
`python3 scripts/check_c3_ninesite_borromean.py`

## Attribution
Original selected-value path and alternation supplied by project user in conversation on 2026-10-22. Linear interpolation, phase shift and exact crossing audit supplied in this implementation. Hopf/Villarceau established references: https://en.wikipedia.org/wiki/Hopf_fibration ; https://link.springer.com/article/10.1007/s00006-019-0960-5 . The knot identification is a classical braid-topology result; no new mathematical theorem is claimed.
