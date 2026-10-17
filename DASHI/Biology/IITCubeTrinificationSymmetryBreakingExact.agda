module DASHI.Biology.IITCubeTrinificationSymmetryBreakingExact where

------------------------------------------------------------------------
-- EXPLICIT SL3^3/TRINIFICATION GENERATOR BREAKS THE SELECTED CUBE IMAGE
--
-- Sibling PR #1106 owns the literal first-Tits/trinification action on M3^3:
--
--   (X,Y,Z) |-> (A X B^-1, B Y C^-1, C Z A^-1),  A,B,C in SL3.
--
-- The selected ternary cube dynamics uses the same 9+9+9 matrix-coordinate
-- shape but restricts outputs to the graph
--
--   Z = Bop Y - Bop^2 X,
--
-- where Bop is the sum of the cyclic row and column shifts on one 3x3 face.
--
-- This module source-writes one completely finite counterexample using
-- A=I, B=I and C=I+E_01 over F3.  C has determinant one and the displayed
-- C^-1 is checked on both sides.  The chosen graph state is sent to a triple
-- whose (0,0) Z-coordinate disagrees with the graph-required value.  Hence the
-- selected 18-dimensional causal image is NOT invariant under the full
-- trinification action: the causal rule is an explicit symmetry-breaking choice
-- inside the exceptional 27 carrier.
--
-- No theorem authority is imported from the unmerged sibling.  The action
-- formula/provenance is recorded separately from this finite local proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- 1. Tiny exact F3 implementation.
------------------------------------------------------------------------

data F3 : Set where
  f0 f1 f2 : F3

add3 : F3 → F3 → F3
add3 f0 x = x
add3 f1 f0 = f1
add3 f1 f1 = f2
add3 f1 f2 = f0
add3 f2 f0 = f2
add3 f2 f1 = f0
add3 f2 f2 = f1

neg3 : F3 → F3
neg3 f0 = f0
neg3 f1 = f2
neg3 f2 = f1

sub3 : F3 → F3 → F3
sub3 x y = add3 x (neg3 y)

mul3 : F3 → F3 → F3
mul3 f0 _ = f0
mul3 f1 x = x
mul3 f2 f0 = f0
mul3 f2 f1 = f2
mul3 f2 f2 = f1

------------------------------------------------------------------------
-- 2. Exact 3x3 matrices.
------------------------------------------------------------------------

record Mat3 : Set where
  constructor mat3
  field
    m00 m01 m02 : F3
    m10 m11 m12 : F3
    m20 m21 m22 : F3
open Mat3 public

zeroM : Mat3
zeroM = mat3 f0 f0 f0 f0 f0 f0 f0 f0 f0

identityM : Mat3
identityM = mat3 f1 f0 f0 f0 f1 f0 f0 f0 f1

e00 : Mat3
e00 = mat3 f1 f0 f0 f0 f0 f0 f0 f0 f0

addM : Mat3 → Mat3 → Mat3
addM a b = mat3
  (add3 (m00 a) (m00 b)) (add3 (m01 a) (m01 b)) (add3 (m02 a) (m02 b))
  (add3 (m10 a) (m10 b)) (add3 (m11 a) (m11 b)) (add3 (m12 a) (m12 b))
  (add3 (m20 a) (m20 b)) (add3 (m21 a) (m21 b)) (add3 (m22 a) (m22 b))

negM : Mat3 → Mat3
negM a = mat3
  (neg3 (m00 a)) (neg3 (m01 a)) (neg3 (m02 a))
  (neg3 (m10 a)) (neg3 (m11 a)) (neg3 (m12 a))
  (neg3 (m20 a)) (neg3 (m21 a)) (neg3 (m22 a))

subM : Mat3 → Mat3 → Mat3
subM a b = addM a (negM b)

dot3 : F3 → F3 → F3 → F3 → F3 → F3 → F3
dot3 a b c x y z = add3 (add3 (mul3 a x) (mul3 b y)) (mul3 c z)

matMul : Mat3 → Mat3 → Mat3
matMul a b = mat3
  (dot3 (m00 a) (m01 a) (m02 a) (m00 b) (m10 b) (m20 b))
  (dot3 (m00 a) (m01 a) (m02 a) (m01 b) (m11 b) (m21 b))
  (dot3 (m00 a) (m01 a) (m02 a) (m02 b) (m12 b) (m22 b))
  (dot3 (m10 a) (m11 a) (m12 a) (m00 b) (m10 b) (m20 b))
  (dot3 (m10 a) (m11 a) (m12 a) (m01 b) (m11 b) (m21 b))
  (dot3 (m10 a) (m11 a) (m12 a) (m02 b) (m12 b) (m22 b))
  (dot3 (m20 a) (m21 a) (m22 a) (m00 b) (m10 b) (m20 b))
  (dot3 (m20 a) (m21 a) (m22 a) (m01 b) (m11 b) (m21 b))
  (dot3 (m20 a) (m21 a) (m22 a) (m02 b) (m12 b) (m22 b))

det3 : Mat3 → F3
det3 a =
  add3
    (sub3
      (mul3 (m00 a) (sub3 (mul3 (m11 a) (m22 a)) (mul3 (m12 a) (m21 a))))
      (mul3 (m01 a) (sub3 (mul3 (m10 a) (m22 a)) (mul3 (m12 a) (m20 a)))))
    (mul3 (m02 a) (sub3 (mul3 (m10 a) (m21 a)) (mul3 (m11 a) (m20 a))))

------------------------------------------------------------------------
-- 3. The selected SL3 shear C=I+E01 and its explicit inverse.
------------------------------------------------------------------------

selectedC : Mat3
selectedC = mat3 f1 f1 f0 f0 f1 f0 f0 f0 f1

selectedCInv : Mat3
selectedCInv = mat3 f1 f2 f0 f0 f1 f0 f0 f0 f1

selectedCDeterminantOne : det3 selectedC ≡ f1
selectedCDeterminantOne = refl

selectedCInverseRight : matMul selectedC selectedCInv ≡ identityM
selectedCInverseRight = refl

selectedCInverseLeft : matMul selectedCInv selectedC ≡ identityM
selectedCInverseLeft = refl

------------------------------------------------------------------------
-- 4. One-face cube operator Bop = cyclic-row-shift + cyclic-column-shift.
------------------------------------------------------------------------

bop : Mat3 → Mat3
bop a = mat3
  (add3 (m10 a) (m01 a)) (add3 (m11 a) (m02 a)) (add3 (m12 a) (m00 a))
  (add3 (m20 a) (m11 a)) (add3 (m21 a) (m12 a)) (add3 (m22 a) (m10 a))
  (add3 (m00 a) (m21 a)) (add3 (m01 a) (m22 a)) (add3 (m02 a) (m20 a))

bop2 : Mat3 → Mat3
bop2 a = bop (bop a)

graphThird : Mat3 → Mat3 → Mat3
graphThird x y = subM (bop y) (bop2 x)

------------------------------------------------------------------------
-- 5. The concrete trinification action with A=B=I, C=selectedC.
------------------------------------------------------------------------

record Sectors27 : Set where
  constructor sectors27
  field
    sectorX sectorY sectorZ : Mat3
open Sectors27 public

selectedTrinificationShear : Sectors27 → Sectors27
selectedTrinificationShear s =
  sectors27
    (sectorX s)
    (matMul (sectorY s) selectedCInv)
    (matMul selectedC (sectorZ s))

selectedCubeGraphState : Sectors27
selectedCubeGraphState =
  sectors27 zeroM e00 (graphThird zeroM e00)

selectedCubeGraphStateIsOnGraph :
  sectorZ selectedCubeGraphState
  ≡ graphThird (sectorX selectedCubeGraphState) (sectorY selectedCubeGraphState)
selectedCubeGraphStateIsOnGraph = refl

transformedState : Sectors27
transformedState = selectedTrinificationShear selectedCubeGraphState

requiredTransformedThird : Mat3
requiredTransformedThird =
  graphThird (sectorX transformedState) (sectorY transformedState)

transformedThird00IsZero : m00 (sectorZ transformedState) ≡ f0
transformedThird00IsZero = refl

graphRequiredThird00IsTwo : m00 requiredTransformedThird ≡ f2
graphRequiredThird00IsTwo = refl

f0NotF2 : f0 ≡ f2 → ⊥
f0NotF2 ()

selectedTrinificationShearBreaksCubeGraph :
  sectorZ transformedState ≡ requiredTransformedThird → ⊥
selectedTrinificationShearBreaksCubeGraph same =
  f0NotF2 (cong m00 same)

------------------------------------------------------------------------
-- 6. Provenance / promotion boundary.
------------------------------------------------------------------------

siblingPR : String
siblingPR = "chboishabba/dashi_agda#1106"

siblingActionFormula : String
siblingActionFormula =
  "(X,Y,Z) -> (A X B^-1, B Y C^-1, C Z A^-1), A,B,C in SL3"

record CubeTrinificationSymmetryBreakingBoundary : Set where
  constructor cube-trinification-symmetry-breaking-boundary
  field
    determinantOneGeneratorUsed : Bool
    explicitInverseChecked : Bool
    graphStateConstructedExactly : Bool
    transformedStateViolatesGraphExactly : Bool
    selectedCubeImageInvariantUnderFullTrinification : Bool
    causalEighteenPlusNineSplitIsExceptionalInvariantByDefinition : Bool
    finiteCounterexampleImportsSiblingAgdaProofAuthority : Bool
    interpretation : String

canonicalCubeTrinificationSymmetryBreakingBoundary :
  CubeTrinificationSymmetryBreakingBoundary
canonicalCubeTrinificationSymmetryBreakingBoundary =
  cube-trinification-symmetry-breaking-boundary
    true true true true false false false
    "The selected cube dynamics defines a proper symmetry-broken subspace of the first-Tits 27 coordinate carrier: an explicit determinant-one trinification shear moves a valid cube-image state off the graph. The full SL3^3/E6 action therefore does not preserve this selected 18+9 causal split."
