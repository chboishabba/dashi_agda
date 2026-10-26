module DASHI.Moonshine.JInvariant369PuncturedSheetModularBraidActionExact where

-- The noncentral eight positions of the *existing* T9 balanced sheet
-- are naturally F3^2 minus zero.  The modular braid word matrix
-- [[13,-8],[-8,5]] reduces mod 3 to [[1,1],[1,2]].
-- Its action consists of TWO 4-cycles and its square is antipodal.
-- This is exact finite modular geometry, NOT a continuous braid on
-- the punctured plane (the original paths traverse the centre).
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Puncture

-- Addition on the repo's native balanced ternary *residue* F3.
add3 : Triadic.KernelTrit → Triadic.KernelTrit → Triadic.KernelTrit
add3 Triadic.negativeTrit Triadic.negativeTrit = Triadic.positiveTrit
add3 Triadic.negativeTrit Triadic.zeroTrit = Triadic.negativeTrit
add3 Triadic.negativeTrit Triadic.positiveTrit = Triadic.zeroTrit
add3 Triadic.zeroTrit y = y
add3 Triadic.positiveTrit Triadic.negativeTrit = Triadic.zeroTrit
add3 Triadic.positiveTrit Triadic.zeroTrit = Triadic.positiveTrit
add3 Triadic.positiveTrit Triadic.positiveTrit = Triadic.negativeTrit

-- [[13,-8],[-8,5]] = [[1,1],[1,2]] mod 3.
-- In F3, 2y=-y, hence (x,y) |-> (x+y, x-y).
modularMatrixOnNine :
  Triadic.NineSheet → Triadic.NineSheet
modularMatrixOnNine (x , y) =
  add3 x y , add3 x (Triadic.negateTrit y)

modularMatrixOnPunctured :
  Puncture.PuncturedNineSheet → Puncture.PuncturedNineSheet
modularMatrixOnPunctured Puncture.negativeEqualDiagonal =
  Puncture.positiveFirstAxis
modularMatrixOnPunctured Puncture.positiveFirstAxis =
  Puncture.positiveEqualDiagonal
modularMatrixOnPunctured Puncture.positiveEqualDiagonal =
  Puncture.negativeFirstAxis
modularMatrixOnPunctured Puncture.negativeFirstAxis =
  Puncture.negativeEqualDiagonal
modularMatrixOnPunctured Puncture.negativeOppositeDiagonal =
  Puncture.positiveSecondAxis
modularMatrixOnPunctured Puncture.positiveSecondAxis =
  Puncture.positiveOppositeDiagonal
modularMatrixOnPunctured Puncture.positiveOppositeDiagonal =
  Puncture.negativeSecondAxis
modularMatrixOnPunctured Puncture.negativeSecondAxis =
  Puncture.negativeOppositeDiagonal

-- The finite matrix really is the action obtained by reducing
-- each coordinate modulo 3 of the integral modular braid image.
puncturedActionIsLiteralMatrix :
  (p : Puncture.PuncturedNineSheet) →
  Puncture.puncturedToNineSheet (modularMatrixOnPunctured p)
  ≡ modularMatrixOnNine (Puncture.puncturedToNineSheet p)
puncturedActionIsLiteralMatrix Puncture.negativeFirstAxis = refl
puncturedActionIsLiteralMatrix Puncture.positiveFirstAxis = refl
puncturedActionIsLiteralMatrix Puncture.negativeSecondAxis = refl
puncturedActionIsLiteralMatrix Puncture.positiveSecondAxis = refl
puncturedActionIsLiteralMatrix Puncture.negativeEqualDiagonal = refl
puncturedActionIsLiteralMatrix Puncture.positiveEqualDiagonal = refl
puncturedActionIsLiteralMatrix Puncture.negativeOppositeDiagonal = refl
puncturedActionIsLiteralMatrix Puncture.positiveOppositeDiagonal = refl

antipode :
  Puncture.PuncturedNineSheet → Puncture.PuncturedNineSheet
antipode Puncture.negativeFirstAxis = Puncture.positiveFirstAxis
antipode Puncture.positiveFirstAxis = Puncture.negativeFirstAxis
antipode Puncture.negativeSecondAxis = Puncture.positiveSecondAxis
antipode Puncture.positiveSecondAxis = Puncture.negativeSecondAxis
antipode Puncture.negativeEqualDiagonal = Puncture.positiveEqualDiagonal
antipode Puncture.positiveEqualDiagonal = Puncture.negativeEqualDiagonal
antipode Puncture.negativeOppositeDiagonal = Puncture.positiveOppositeDiagonal
antipode Puncture.positiveOppositeDiagonal = Puncture.negativeOppositeDiagonal

modularSquareIsAntipode :
  (p : Puncture.PuncturedNineSheet) →
  modularMatrixOnPunctured (modularMatrixOnPunctured p)
  ≡ antipode p
modularSquareIsAntipode Puncture.negativeFirstAxis = refl
modularSquareIsAntipode Puncture.positiveFirstAxis = refl
modularSquareIsAntipode Puncture.negativeSecondAxis = refl
modularSquareIsAntipode Puncture.positiveSecondAxis = refl
modularSquareIsAntipode Puncture.negativeEqualDiagonal = refl
modularSquareIsAntipode Puncture.positiveEqualDiagonal = refl
modularSquareIsAntipode Puncture.negativeOppositeDiagonal = refl
modularSquareIsAntipode Puncture.positiveOppositeDiagonal = refl

modularFourthIsIdentity :
  (p : Puncture.PuncturedNineSheet) →
  modularMatrixOnPunctured
    (modularMatrixOnPunctured
      (modularMatrixOnPunctured (modularMatrixOnPunctured p)))
  ≡ p
modularFourthIsIdentity Puncture.negativeFirstAxis = refl
modularFourthIsIdentity Puncture.positiveFirstAxis = refl
modularFourthIsIdentity Puncture.negativeSecondAxis = refl
modularFourthIsIdentity Puncture.positiveSecondAxis = refl
modularFourthIsIdentity Puncture.negativeEqualDiagonal = refl
modularFourthIsIdentity Puncture.positiveEqualDiagonal = refl
modularFourthIsIdentity Puncture.negativeOppositeDiagonal = refl
modularFourthIsIdentity Puncture.positiveOppositeDiagonal = refl

modularHasNoFixedPuncturedPoint :
  (p : Puncture.PuncturedNineSheet) →
  modularMatrixOnPunctured p ≡ p → ⊥
modularHasNoFixedPuncturedPoint Puncture.negativeFirstAxis ()
modularHasNoFixedPuncturedPoint Puncture.positiveFirstAxis ()
modularHasNoFixedPuncturedPoint Puncture.negativeSecondAxis ()
modularHasNoFixedPuncturedPoint Puncture.positiveSecondAxis ()
modularHasNoFixedPuncturedPoint Puncture.negativeEqualDiagonal ()
modularHasNoFixedPuncturedPoint Puncture.positiveEqualDiagonal ()
modularHasNoFixedPuncturedPoint Puncture.negativeOppositeDiagonal ()
modularHasNoFixedPuncturedPoint Puncture.positiveOppositeDiagonal ()

-- Native eight-position puncture, modular action order four, and
-- nonzero-point condition are now on the SAME literal finite carrier.
-- Analytic lattice actions and physical braid/VOA actions still require
-- their own map and theorem.
