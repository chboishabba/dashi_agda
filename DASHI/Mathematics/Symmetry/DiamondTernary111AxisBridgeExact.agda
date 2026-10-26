module DASHI.Mathematics.Symmetry.DiamondTernary111AxisBridgeExact where

-- Crosswalk: 111 base-three = 13 is a PLACE-VALUE value; +++
-- as a balanced-ternary triad is instead a signed 3-vector.
-- The common digits are a typed correspondence, not a physical law.
--
-- Prior sources: AllOnesPadicThresholdBoundary; BalancedTernaryStageSymmetryExact;
-- DiamondNVFourAxisPermutationExact (PR #1261); NV axis work (PR #1238).
-- Classical 111 crystal directions and antipodal lines have external
-- crystallographic prior art. No spin-Hamiltonian symmetry is inferred.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.AllOnesPadicThresholdBoundary as Prefix
import DASHI.Mathematics.Symmetry.DiamondNVFourAxisPermutationExact as NV

data Sign : Set where
  plus minus : Sign

flip : Sign → Sign
flip plus = minus
flip minus = plus

flipTwice : (s : Sign) → flip (flip s) ≡ s
flipTwice plus = refl
flipTwice minus = refl

record Corner111 : Set where
  constructor corner
  field
    x y z : Sign
open Corner111 public

opposite : Corner111 → Corner111
opposite (corner x y z) = corner (flip x) (flip y) (flip z)

oppositeTwice : (p : Corner111) → opposite (opposite p) ≡ p
oppositeTwice (corner plus plus plus) = refl
oppositeTwice (corner plus plus minus) = refl
oppositeTwice (corner plus minus plus) = refl
oppositeTwice (corner plus minus minus) = refl
oppositeTwice (corner minus plus plus) = refl
oppositeTwice (corner minus plus minus) = refl
oppositeTwice (corner minus minus plus) = refl
oppositeTwice (corner minus minus minus) = refl

-- The projective quotient of the 8 cube corners by antipodal sign
-- has exactly the four NV axes. Use even-minus representatives.
axis : Corner111 → NV.Axis
axis (corner plus plus plus) = NV.aaa
axis (corner plus minus minus) = NV.abb
axis (corner minus plus minus) = NV.bab
axis (corner minus minus plus) = NV.bba
axis (corner minus minus minus) = NV.aaa
axis (corner minus plus plus) = NV.abb
axis (corner plus minus plus) = NV.bab
axis (corner plus plus minus) = NV.bba

axisAntipodal : (p : Corner111) → axis (opposite p) ≡ axis p
axisAntipodal (corner plus plus plus) = refl
axisAntipodal (corner plus plus minus) = refl
axisAntipodal (corner plus minus plus) = refl
axisAntipodal (corner plus minus minus) = refl
axisAntipodal (corner minus plus plus) = refl
axisAntipodal (corner minus plus minus) = refl
axisAntipodal (corner minus minus plus) = refl
axisAntipodal (corner minus minus minus) = refl

representative : NV.Axis → Corner111
representative NV.aaa = corner plus plus plus
representative NV.abb = corner plus minus minus
representative NV.bab = corner minus plus minus
representative NV.bba = corner minus minus plus

axisRepresentative : (a : NV.Axis) → axis (representative a) ≡ a
axisRepresentative NV.aaa = refl
axisRepresentative NV.abb = refl
axisRepresentative NV.bab = refl
axisRepresentative NV.bba = refl

-- Unoriented signed lines carry spatial C3 and cubic C4 permutations.
turn3 : Corner111 → Corner111
turn3 (corner x y z) = corner y z x

turn3Thrice : (p : Corner111) → turn3 (turn3 (turn3 p)) ≡ p
turn3Thrice (corner x y z) = refl

turn4 : Corner111 → Corner111
turn4 (corner x y z) = corner (flip y) x z

turn4Four : (p : Corner111) →
  turn4 (turn4 (turn4 (turn4 p))) ≡ p
turn4Four (corner plus plus plus) = refl
turn4Four (corner plus plus minus) = refl
turn4Four (corner plus minus plus) = refl
turn4Four (corner plus minus minus) = refl
turn4Four (corner minus plus plus) = refl
turn4Four (corner minus plus minus) = refl
turn4Four (corner minus minus plus) = refl
turn4Four (corner minus minus minus) = refl

-- The diagram commutes after quotient by ±1.
axisTurn3 : (p : Corner111) → axis (turn3 p) ≡ NV.cycle (axis p)
axisTurn3 (corner plus plus plus) = refl
axisTurn3 (corner plus plus minus) = refl
axisTurn3 (corner plus minus plus) = refl
axisTurn3 (corner plus minus minus) = refl
axisTurn3 (corner minus plus plus) = refl
axisTurn3 (corner minus plus minus) = refl
axisTurn3 (corner minus minus plus) = refl
axisTurn3 (corner minus minus minus) = refl

axisTurn4 : (p : Corner111) → axis (turn4 p) ≡ NV.quarterZ (axis p)
axisTurn4 (corner plus plus plus) = refl
axisTurn4 (corner plus plus minus) = refl
axisTurn4 (corner plus minus plus) = refl
axisTurn4 (corner plus minus minus) = refl
axisTurn4 (corner minus plus plus) = refl
axisTurn4 (corner minus plus minus) = refl
axisTurn4 (corner minus minus plus) = refl
axisTurn4 (corner minus minus minus) = refl

signDigit : Sign → BT.BalancedDigit
signDigit plus = BT.pos
signDigit minus = BT.neg

toBalancedTriad : Corner111 → BT.TriadPattern
toBalancedTriad (corner x y z) =
  BT.triad (signDigit x) (signDigit y) (signDigit z)

allPositiveIsNativeTriad :
  toBalancedTriad (corner plus plus plus) ≡ BT.allPositive
allPositiveIsNativeTriad = refl

allOnesBaseThreeIsThirteen : Prefix.allOnesPrefix 3 ≡ 13
allOnesBaseThreeIsThirteen = Prefix.allOnesPrefix3

-- The 13 and the spatial [1,1,1] are two different observers of
-- digit data: radix evaluation vs three signed coordinate slots.
-- The 27 trit triples include zeros and cannot be bijected with
-- the 8 sign triples without a residual/restriction.
