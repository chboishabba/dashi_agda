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


------------------------------------------------------------------------
-- Selected global PSU3 fractional instanton cancellation:
-- all 3 projected PSU3 factors of (SU3^3)/Z3_diag inherit the
-- SAME class B in H²(X,Z3). In standard PSU3 instanton convention
-- fractional q_i ≡ (int B cup B)/3 mod1. Therefore equal-weight
-- sum q_c + q_L + q_R is INTEGRAL modulo one, for all three
-- residues of B². This is a finite Z3 source computation, NOT
-- a theorem of the 5D physical CS or global APS eta invariant.
-- Script: check_kk_e6_z3_fractional_instanton_mixed_wz.py
------------------------------------------------------------------------

threeProjectedFractionalChargesSumToZeroModThree :
  (r : ZThree) → addZ3 r (addZ3 r r) ≡ z0
threeProjectedFractionalChargesSumToZeroModThree z0 = refl
threeProjectedFractionalChargesSumToZeroModThree z1 = refl
threeProjectedFractionalChargesSumToZeroModThree z2 = refl

individualFractionalChargeCanRemainNonzero :
  addZ3 z1 z0 ≡ z1
individualFractionalChargeCanRemainNonzero = refl

allQuotientMixedAbelianSpinCSPeriodsCertified : Bool
allQuotientMixedAbelianSpinCSPeriodsCertified = false


------------------------------------------------------------------------
-- 2026-10-26 ORBIFOLD-EVEN S2 CLUTCH / HIGGS-LINE BIDI
-- Physical owner #1241: check_kk_e6_orbifold_even_quotient_s2_clutch.py
-- first-Tits 27 original action owner #1106, not duplicated.
--
-- The selected parity-even boundary group H=H0/Z3_diag admits a
-- clutch loop lifted to H0 from 1 to diagonal omega. Varying a
-- further closed SU3_L torus turn does NOT alter its Z3 obstruction,
-- but changes the C33 associated line degree from zero to -2.
-- Finite consumer witness only: the topology and Chern degree are
-- external premises justified in the accompanying source derivation,
-- NOT kernel-constructed principal bundles or cohomology here.
------------------------------------------------------------------------

data OrbifoldEvenClutchRepresentative : Set where
  baseDiagonalCentralLoop
  extraLeftTorusTurn
  extraOneEntryLeftTurn
  extraOneEntryRightTurn : OrbifoldEvenClutchRepresentative

sameZThreeLiftingClass :
  OrbifoldEvenClutchRepresentative → ZThree
sameZThreeLiftingClass _ = z1

-- All four loops have the SAME nontrivial central lift obstruction.
-- The actual boundary U2 torus lets the two doublet entries wind
-- INDEPENDENTLY. Thus Chi33 determinant-ratio clutch degrees are
-- 0, -2, -1, +1 (chosen orientation); the old even-degree statement
-- applies ONLY to the restricted equal-doublet-torus winding.
-- Labels here are externally computed clutch-degree facts, not
-- kernel-constructed line bundles or a differential-character WZ.
chi33LineDegreeZero :
  OrbifoldEvenClutchRepresentative → Bool
chi33LineDegreeZero baseDiagonalCentralLoop = true
chi33LineDegreeZero extraLeftTorusTurn = false
chi33LineDegreeZero extraOneEntryLeftTurn = false
chi33LineDegreeZero extraOneEntryRightTurn = false

chi33LineDegreeOdd :
  OrbifoldEvenClutchRepresentative → Bool
chi33LineDegreeOdd baseDiagonalCentralLoop = false
chi33LineDegreeOdd extraLeftTorusTurn = false
chi33LineDegreeOdd extraOneEntryLeftTurn = true
chi33LineDegreeOdd extraOneEntryRightTurn = true

sameDeckDoesNotDetermineChi33WindingParity :
  Transport.ClaimNonTransportWitness
    sameZThreeLiftingClass chi33LineDegreeOdd
sameDeckDoesNotDetermineChi33WindingParity =
  Descent.consumerNonDescentWitness
    baseDiagonalCentralLoop extraOneEntryLeftTurn
    refl falseNotTrue

sameQuotientObstructionDoesNotDetermineChi33Line :
  Transport.ClaimNonTransportWitness
    sameZThreeLiftingClass chi33LineDegreeZero
sameQuotientObstructionDoesNotDetermineChi33Line =
  Descent.consumerNonDescentWitness
    extraLeftTorusTurn baseDiagonalCentralLoop
    refl falseNotTrue

unpatchedChi33PhaseOnlyWZDefinedOnEveryBundle : Bool
unpatchedChi33PhaseOnlyWZDefinedOnEveryBundle = false
