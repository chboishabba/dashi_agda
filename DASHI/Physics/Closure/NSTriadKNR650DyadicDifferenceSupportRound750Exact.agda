{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceSupportRound750Exact where

------------------------------------------------------------------------
-- ROUND750 / SUPPORT OF THE TWO DYADIC PRODUCTION DIFFERENCES
--
-- R748/R749 expose the actual critical-production correction through
--
--   (lambda~_k - lambda~_q) PairPower_k
-- + (lambda~_p - lambda~_q) PairPower_p.
--
-- This owner records the exact support fact:
--
-- * if k,p,q are nonzero and lie in the same dyadic shell, the two selected
--   dyadic weights are equal;
-- * therefore the whole paired production two-difference cell is zero;
-- * consequently the R749 local W2 nonlinear cell reduces to
--
--       3 * NestedOrbit(beta)
--
--   on same-shell nonzero incidences.
--
-- No estimate or shell-separation lower bound is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _*_; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744

F : C3.RealField _
F = Rational.rationalRealField

modeEqualZeroFalseFromNonzero :
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  Output.modeEqual mode Z3.zeroMode ≡ false
modeEqualZeroFalseFromNonzero mode nonzero
  with Output.modeEqual mode Z3.zeroMode in decision
... | false = refl
... | true =
  ⊥-elim
    (Z3.notZero nonzero (Output.modeEqualSound decision))

dyadicWeightEqualAtSameShell :
  (left right : Z3.FourierMode) →
  Shell.shellIndex left ≡ Shell.shellIndex right →
  Fold.dyadicCriticalWeight left ≡ Fold.dyadicCriticalWeight right
dyadicWeightEqualAtSameShell left right shellEqual
  rewrite shellEqual = refl

selectedDyadicWeightEqualAtSameNonzeroShell :
  (left right : Z3.FourierMode) →
  Z3.NonZeroMode left →
  Z3.NonZeroMode right →
  Shell.shellIndex left ≡ Shell.shellIndex right →
  R748.selectedDyadicWeight left ≡ R748.selectedDyadicWeight right
selectedDyadicWeightEqualAtSameNonzeroShell
    left right leftNonzero rightNonzero shellEqual
  rewrite modeEqualZeroFalseFromNonzero left leftNonzero
        | modeEqualZeroFalseFromNonzero right rightNonzero =
  dyadicWeightEqualAtSameShell left right shellEqual

pairedProductionTwoDifferenceZeroWhenSelectedWeightsEqual :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (tau : Physical.PhysicalTriadIncidence) →
  R748.selectedDyadicWeight (Physical.k tau)
    ≡ R748.selectedDyadicWeight (Physical.q tau) →
  R748.selectedDyadicWeight (Physical.p tau)
    ≡ R748.selectedDyadicWeight (Physical.q tau) →
  R748.pairedProductionTwoDifferenceCell system tau ≡ 0ℚ
pairedProductionTwoDifferenceZeroWhenSelectedWeightsEqual
    system tau kq pq
  rewrite kq | pq = solve []

pairedProductionTwoDifferenceZeroOnSameNonzeroShell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.k tau) →
  Z3.NonZeroMode (Physical.p tau) →
  Z3.NonZeroMode (Physical.q tau) →
  Shell.shellIndex (Physical.k tau)
    ≡ Shell.shellIndex (Physical.q tau) →
  Shell.shellIndex (Physical.p tau)
    ≡ Shell.shellIndex (Physical.q tau) →
  R748.pairedProductionTwoDifferenceCell system tau ≡ 0ℚ
pairedProductionTwoDifferenceZeroOnSameNonzeroShell
    system tau kNonzero pNonzero qNonzero kqShell pqShell =
  pairedProductionTwoDifferenceZeroWhenSelectedWeightsEqual
    system tau
    (selectedDyadicWeightEqualAtSameNonzeroShell
      (Physical.k tau) (Physical.q tau)
      kNonzero qNonzero kqShell)
    (selectedDyadicWeightEqualAtSameNonzeroShell
      (Physical.p tau) (Physical.q tau)
      pNonzero qNonzero pqShell)

------------------------------------------------------------------------
-- Generic local consumer used directly by R749.
------------------------------------------------------------------------

differenceAlignedCellReducesToNestedWhenProductionZero :
  (nested production : ℚ) →
  production ≡ 0ℚ →
  R744.three * nested - production
  ≡ R744.three * nested
differenceAlignedCellReducesToNestedWhenProductionZero
    nested production productionZero
  rewrite productionZero = solve []

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round750TwoDifferenceProductionVanishesOnSameNonzeroShell : Bool
round750TwoDifferenceProductionVanishesOnSameNonzeroShell = true

round750OnlyCrossShellOrZeroLegGeometryCanCarryProductionDifference : Bool
round750OnlyCrossShellOrZeroLegGeometryCanCarryProductionDifference = true

round750IntroducesEstimate : Bool
round750IntroducesEstimate = false

round750IntroducesShellSeparationLowerBound : Bool
round750IntroducesShellSeparationLowerBound = false

round750ClayPromotion : Bool
round750ClayPromotion = false

round750TwoDifferenceProductionVanishesOnSameNonzeroShellIsTrue :
  round750TwoDifferenceProductionVanishesOnSameNonzeroShell ≡ true
round750TwoDifferenceProductionVanishesOnSameNonzeroShellIsTrue = refl

round750OnlyCrossShellOrZeroLegGeometryCanCarryProductionDifferenceIsTrue :
  round750OnlyCrossShellOrZeroLegGeometryCanCarryProductionDifference ≡ true
round750OnlyCrossShellOrZeroLegGeometryCanCarryProductionDifferenceIsTrue = refl

round750IntroducesEstimateIsFalse :
  round750IntroducesEstimate ≡ false
round750IntroducesEstimateIsFalse = refl

round750IntroducesShellSeparationLowerBoundIsFalse :
  round750IntroducesShellSeparationLowerBound ≡ false
round750IntroducesShellSeparationLowerBoundIsFalse = refl

round750ClayPromotionIsFalse :
  round750ClayPromotion ≡ false
round750ClayPromotionIsFalse = refl
