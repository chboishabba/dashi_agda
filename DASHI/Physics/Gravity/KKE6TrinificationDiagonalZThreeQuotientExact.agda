module DASHI.Physics.Gravity.KKE6TrinificationDiagonalZThreeQuotientExact where

------------------------------------------------------------------------
-- 2026-10-25 SOURCE FAITHFUL global first-Tits 27 central kernel.
-- E6 #1106 original M3^3 representation ACTUALLY uses
-- (X,Y,Z) -> (A X B^-1, B Y C^-1, C Z A^-1).
-- Hence the three SU3 central exponents (a,b,c) act on
-- 27=(3,bar3,1)+(bar3,1,3)+(1,3,bar3)
-- by (a-b,c-a,b-c) mod3. The kernel is EXACTLY diagonal Z3.
-- This module doesn't import unmerged original E6 #1106 Agda.
--
-- As a result, the faithful gauge action is SU3^3 / Z3_diag.
-- A T2 clock/shift pair can commute in quotient while its
-- SU3³ lifts have commutator (omega,omega,omega), so CP3 etc
-- LIFTABLE bundle index tests DO NOT cover all quotient bundles.
-- Actual quotient bundle/gauge eta, spin CS remains OPEN.
-- Original E6 branching: Slansky, Phys Reports 79 (1981).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

data ZThree : Set where
  z0 z1 z2 : ZThree

addZ3 : ZThree → ZThree → ZThree
addZ3 z0 x = x
addZ3 z1 z0 = z1
addZ3 z1 z1 = z2
addZ3 z1 z2 = z0
addZ3 z2 z0 = z2
addZ3 z2 z1 = z0
addZ3 z2 z2 = z1

negZ3 : ZThree → ZThree
negZ3 z0 = z0
negZ3 z1 = z2
negZ3 z2 = z1

subtractZ3 : ZThree → ZThree → ZThree
subtractZ3 a b = addZ3 a (negZ3 b)

sameZ3 : ZThree → ZThree → Bool
sameZ3 z0 z0 = true
sameZ3 z1 z1 = true
sameZ3 z2 z2 = true
sameZ3 _ _ = false

andBool : Bool → Bool → Bool
andBool true x = x
andBool false _ = false

-- Exactly the three 3x3 block central phases, not generic E6 centre.
centralTrivialOn27 : ZThree → ZThree → ZThree → Bool
centralTrivialOn27 a b c =
  andBool (sameZ3 (subtractZ3 a b) z0)
    (andBool (sameZ3 (subtractZ3 c a) z0)
      (sameZ3 (subtractZ3 b c) z0))

diagonalZThree : ZThree → ZThree → ZThree → Bool
diagonalZThree a b c =
  andBool (sameZ3 a b) (sameZ3 b c)

-- COMPLETE 3^3=27 centre assignments, source-literal 27-carrier
-- actual group kernel condition, no numeric/cardinality shortcut.
centreKernelIffDiagonal :
  (a b c : ZThree) →
  centralTrivialOn27 a b c ≡ diagonalZThree a b c
centreKernelIffDiagonal z0 z0 z0 = refl
centreKernelIffDiagonal z0 z0 z1 = refl
centreKernelIffDiagonal z0 z0 z2 = refl
centreKernelIffDiagonal z0 z1 z0 = refl
centreKernelIffDiagonal z0 z1 z1 = refl
centreKernelIffDiagonal z0 z1 z2 = refl
centreKernelIffDiagonal z0 z2 z0 = refl
centreKernelIffDiagonal z0 z2 z1 = refl
centreKernelIffDiagonal z0 z2 z2 = refl
centreKernelIffDiagonal z1 z0 z0 = refl
centreKernelIffDiagonal z1 z0 z1 = refl
centreKernelIffDiagonal z1 z0 z2 = refl
centreKernelIffDiagonal z1 z1 z0 = refl
centreKernelIffDiagonal z1 z1 z1 = refl
centreKernelIffDiagonal z1 z1 z2 = refl
centreKernelIffDiagonal z1 z2 z0 = refl
centreKernelIffDiagonal z1 z2 z1 = refl
centreKernelIffDiagonal z1 z2 z2 = refl
centreKernelIffDiagonal z2 z0 z0 = refl
centreKernelIffDiagonal z2 z0 z1 = refl
centreKernelIffDiagonal z2 z0 z2 = refl
centreKernelIffDiagonal z2 z1 z0 = refl
centreKernelIffDiagonal z2 z1 z1 = refl
centreKernelIffDiagonal z2 z1 z2 = refl
centreKernelIffDiagonal z2 z2 z0 = refl
centreKernelIffDiagonal z2 z2 z1 = refl
centreKernelIffDiagonal z2 z2 z2 = refl

diagonalZThreeActsTrivially :
  (a : ZThree) → centralTrivialOn27 a a a ≡ true
diagonalZThreeActsTrivially z0 = refl
diagonalZThreeActsTrivially z1 = refl
diagonalZThreeActsTrivially z2 = refl

data GaugeGlobalForm : Set where
  unfactoredSUThreeCubed
  faithfulDiagonalZThreeQuotient : GaugeGlobalForm

sameAlgebraAndMatterDimension : GaugeGlobalForm → Nat
sameAlgebraAndMatterDimension _ = 27

-- Original nonliftable quotient T² holonomy:
-- C=diag(1,ω,ω²), S=cyclic shift, CS=ωSC.
-- [(C,C,C),(S,S,S)] commute in faithful quotient,
-- NOT as SU3³ cover holonomies.
selectedClockShiftIsCommutingGaugePair : GaugeGlobalForm → Bool
selectedClockShiftIsCommutingGaugePair unfactoredSUThreeCubed = false
selectedClockShiftIsCommutingGaugePair faithfulDiagonalZThreeQuotient = true

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

same27DoesNotDetermineGlobalGaugeBundle :
  Transport.ClaimNonTransportWitness
    sameAlgebraAndMatterDimension
    selectedClockShiftIsCommutingGaugePair
same27DoesNotDetermineGlobalGaugeBundle =
  Descent.consumerNonDescentWitness
    unfactoredSUThreeCubed
    faithfulDiagonalZThreeQuotient refl falseNotTrue

liftableBundleSpinIndexPaysGlobalCS : Bool
liftableBundleSpinIndexPaysGlobalCS = false
