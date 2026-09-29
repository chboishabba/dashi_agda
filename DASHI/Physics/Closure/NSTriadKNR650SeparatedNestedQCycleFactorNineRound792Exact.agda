{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedNestedQCycleFactorNineRound792Exact where

------------------------------------------------------------------------
-- ROUND792 / THE SEPARATED THREE-PROFILE NESTED q-CYCLE IS FACTOR NINE
--
-- R791 proves on the fully-separated mask:
--
--   sum PairedNestedOrbit = 3 * sum PairedBaseProductRule.
--
-- qEnergyLeg is an exact enumeration permutation.  Therefore the three
-- q-positions beta,q beta,q^2 beta have equal masked paired-nested folds.
-- Summing those three positions gives exactly
--
--   sum CycleNested = 9 * sum PairedBaseProductRule.
--
-- This is still exact signed algebra; no estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedNestedOrbitNormalFormRound763Exact as R763
import DASHI.Physics.Closure.NSTriadKNR650GlobalPairedNestedProductRuleRound772Exact as R772
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPairedNestedProductRuleRound791Exact as R791

F : C3.RealField _
F = Rational.rationalRealField

nine : ℚ
nine = 9

module SeparatedNestedQCycle
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Sep = R791.SeparatedGlobalPairedNested
    physicalSystem S L H velocityTransverse

  items : List Physical.PhysicalTriadIncidence
  items = Sep.items

  q1Cell : Physical.PhysicalTriadIncidence → ℚ
  q1Cell beta =
    Sep.maskedPairedOrbitCell (Orbit.qEnergyLeg beta)

  q2Cell : Physical.PhysicalTriadIncidence → ℚ
  q2Cell beta =
    Sep.maskedPairedOrbitCell
      (Orbit.qEnergyLeg (Orbit.qEnergyLeg beta))

  cycleCell : Physical.PhysicalTriadIncidence → ℚ
  cycleCell beta =
    Sep.maskedPairedOrbitCell beta + q1Cell beta + q2Cell beta

  baseFold : ℚ
  baseFold =
    R38.foldPower Sep.maskedPairedOrbitCell items

  q1Fold : ℚ
  q1Fold =
    R38.foldPower q1Cell items

  q2Fold : ℚ
  q2Fold =
    R38.foldPower q2Cell items

  cycleFold : ℚ
  cycleFold =
    R38.foldPower cycleCell items

  foldQInvariant :
    (value : Physical.PhysicalTriadIncidence → ℚ) →
    R38.foldPower (λ beta → value (Orbit.qEnergyLeg beta)) items
    ≡ R38.foldPower value items
  foldQInvariant value =
    trans
      (sym (R38.foldMap value Orbit.qEnergyLeg items))
      (R38.foldPermutationInvariant value
        (R38.qEnergyLegEnumerationPermutation Sep.cutoff))

  q1FoldIsBase : q1Fold ≡ baseFold
  q1FoldIsBase =
    foldQInvariant Sep.maskedPairedOrbitCell

  q2FoldIsBase : q2Fold ≡ baseFold
  q2FoldIsBase =
    trans
      (foldQInvariant q1Cell)
      q1FoldIsBase

  cycleFoldSplits :
    cycleFold ≡ baseFold + q1Fold + q2Fold
  cycleFoldSplits =
    go items
    where
    go :
      (xs : List Physical.PhysicalTriadIncidence) →
      R38.foldPower cycleCell xs
      ≡
      R38.foldPower Sep.maskedPairedOrbitCell xs
        + R38.foldPower q1Cell xs
        + R38.foldPower q2Cell xs
    go [] = refl
    go (beta ∷ rest) =
      trans
        (cong (cycleCell beta +_) (go rest))
        (solve
          ( Sep.maskedPairedOrbitCell beta
          ∷ q1Cell beta
          ∷ q2Cell beta
          ∷ R38.foldPower Sep.maskedPairedOrbitCell rest
          ∷ R38.foldPower q1Cell rest
          ∷ R38.foldPower q2Cell rest
          ∷ []))

  cycleFoldIsThreeBase :
    cycleFold ≡ R772.three * baseFold
  cycleFoldIsThreeBase =
    trans
      cycleFoldSplits
      (trans
        (cong
          (λ selected → baseFold + selected + q2Fold)
          q1FoldIsBase)
        (trans
          (cong
            (λ selected → baseFold + baseFold + selected)
            q2FoldIsBase)
          (solve (R772.three ∷ baseFold ∷ []))))

  cycleFoldIsNinePairedBase :
    cycleFold
    ≡ nine * R38.foldPower Sep.maskedPairedBaseRow items
  cycleFoldIsNinePairedBase =
    trans
      cycleFoldIsThreeBase
      (trans
        (cong
          (R772.three *_)
          Sep.separatedPairedNestedIsThreePairedBase)
        (solve
          ( R772.three
          ∷ nine
          ∷ R38.foldPower Sep.maskedPairedBaseRow items
          ∷ [])))

round792SeparatedNestedQCycleIsFactorNine : Bool
round792SeparatedNestedQCycleIsFactorNine = true

round792IntroducesEstimate : Bool
round792IntroducesEstimate = false

round792W2Closed : Bool
round792W2Closed = false

round792ClayPromotion : Bool
round792ClayPromotion = false

round792SeparatedNestedQCycleIsFactorNineIsTrue :
  round792SeparatedNestedQCycleIsFactorNine ≡ true
round792SeparatedNestedQCycleIsFactorNineIsTrue = refl

round792IntroducesEstimateIsFalse :
  round792IntroducesEstimate ≡ false
round792IntroducesEstimateIsFalse = refl

round792W2ClosedIsFalse :
  round792W2Closed ≡ false
round792W2ClosedIsFalse = refl

round792ClayPromotionIsFalse :
  round792ClayPromotion ≡ false
round792ClayPromotionIsFalse = refl
