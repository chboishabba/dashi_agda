module DASHI.Physics.Closure.NSTriadKNCenteredCovarianceR290DynamicNormalFormExact where

------------------------------------------------------------------------
-- CENTERED COVARIANCE -> R290 DYNAMIC NORMAL FORM
--
-- The fixed-output physical-rate normal form reduces the R229 covariance leaf
-- to one centered-frequency multiplier work
--
--   (nu/2) W(M,C).
--
-- The rate-weighted coherent-row decomposition and the literal R390 pair
-- enumeration now put that SAME scalar on the R290 double-mixed carrier:
--
--   (nu/2) W(M,C)
--     = diagonalRateGram
--       + offDiagonalPairRateGram
--       - lambda_k W(M,M)
--
-- and the preceding R290 splice gives
--
--   offDiagonalPairRateGram
--     = sum nonlinearGramRemainder - sum gramTangent.
--
-- Therefore the full centered covariance has the exact dynamic normal form
--
--   (nu/2) W(M,C)
--     = diagonalRateGram
--       + sum nonlinearGramRemainder
--       - sum gramTangent
--       - lambda_k W(M,M).
--
-- This is the precise meeting point of the R229/R414 and R290/R503 lanes.
-- It is NOT an identification with the unweighted R503 Gram debt: one physical
-- pair-rate remains.  No inequality, absolute value, cardinality bound,
-- integration, or Clay promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import Data.Rational using (Positive)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalOutputRateNormalFormExact as OutputRate
import DASHI.Physics.Closure.NSTriadKNFixedOutputRateWeightedGramRowDecompositionExact as Row
import DASHI.Physics.Closure.NSTriadKNFixedOutputRateWeightedGramToR290Exact as R290Bridge

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalCenteredR290
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (positivePairRate :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      Positive
        (R291.pairRate
          (R389.DoubleMixedPair.physicalDoubleMixedPair
            physicalSystem S alpha beta))) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Bridge = R290Bridge.LiteralPairs physicalSystem S positivePairRate

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  nu = Field30.viscosity physicalSystem

  rate : Physical.PhysicalTriadIncidence → ℚ
  rate = Bridge.rate

  value : Physical.PhysicalTriadIncidence → C3.Complex3 F
  value = Bridge.value

  centeredMultiplier : Physical.PhysicalTriadIncidence → ℚ
  centeredMultiplier = Vector.centeredFrequencyMultiplier E

  itemsAt : Nat → Z3.FourierMode → List Physical.PhysicalTriadIncidence
  itemsAt cutoff output = Output.physicalOutputFiber cutoff output

  mixedAt : Nat → Z3.FourierMode → C3.Complex3 F
  mixedAt cutoff output = R224.foldVector value (itemsAt cutoff output)

  centeredVectorAt : Nat → Z3.FourierMode → C3.Complex3 F
  centeredVectorAt cutoff output =
    Vector.weightedVectorSum centeredMultiplier value (itemsAt cutoff output)

  workAt :
    Nat → Z3.FourierMode →
    Physical.PhysicalTriadIncidence → ℚ
  workAt cutoff output =
    Cov.cellWork (mixedAt cutoff output) value

  rateIsLiteralViscousCellRate :
    (tau : Physical.PhysicalTriadIncidence) →
    rate tau
    ≡ Cov.cellRate (Centered.modalViscousRate nu I) tau
  rateIsLiteralViscousCellRate tau = refl

  centeredRowIdentity :
    (cutoff : Nat) (output : Z3.FourierMode) →
    OutputRate.halfViscosity nu
      * Work.coherentWork
          (mixedAt cutoff output)
          (centeredVectorAt cutoff output)
    ≡
      Row.rateDiagonalGram rate value (itemsAt cutoff output)
      + Row.pairRateOffDiagonalGram rate value (itemsAt cutoff output)
      - OutputRate.outputHeatRate nu I output
          * Work.coherentWork
              (mixedAt cutoff output)
              (mixedAt cutoff output)
  centeredRowIdentity cutoff output =
    let
      items = itemsAt cutoff output
      mixed = mixedAt cutoff output
      centeredVector = centeredVectorAt cutoff output
      work = workAt cutoff output
      common = OutputRate.outputHeatRate nu I output
      halfNu = OutputRate.halfViscosity nu

      row :
        Row.rateDiagonalGram rate value items
          + Row.pairRateOffDiagonalGram rate value items
        ≡ Work.coherentWork mixed
            (Vector.weightedVectorSum rate value items)
      row =
        sym (Row.rateWeightedCoherentWorkDecomposition rate value items)

      weightedWork :
        Work.coherentWork mixed
            (Vector.weightedVectorSum rate value items)
        ≡ Cov.weightedWorkSum rate work items
      weightedWork =
        Vector.weightedVectorWorkMeaning mixed rate value items

      split :
        Cov.weightedWorkSum rate work items
        ≡ common * Cov.workSum work items
          + halfNu * Cov.weightedWorkSum centeredMultiplier work items
      split =
        OutputRate.literalWeightedRateWorkSplit
          E I nu work cutoff output

      self :
        Cov.workSum work items
        ≡ Work.coherentWork mixed mixed
      self =
        Cov.workSumAgainstFold mixed value items

      centered :
        Cov.weightedWorkSum centeredMultiplier work items
        ≡ Work.coherentWork mixed centeredVector
      centered =
        sym
          (Vector.weightedVectorWorkMeaning
            mixed centeredMultiplier value items)

      rowSplit :
        Row.rateDiagonalGram rate value items
          + Row.pairRateOffDiagonalGram rate value items
        ≡ common * Work.coherentWork mixed mixed
          + halfNu * Work.coherentWork mixed centeredVector
      replaceSelf :
        common * Cov.workSum work items
          + halfNu * Cov.weightedWorkSum centeredMultiplier work items
        ≡ common * Work.coherentWork mixed mixed
          + halfNu * Cov.weightedWorkSum centeredMultiplier work items
      replaceSelf =
        cong
          (λ pair →
            common * pair
              + halfNu * Cov.weightedWorkSum centeredMultiplier work items)
          self

      replaceCentered :
        common * Work.coherentWork mixed mixed
          + halfNu * Cov.weightedWorkSum centeredMultiplier work items
        ≡ common * Work.coherentWork mixed mixed
          + halfNu * Work.coherentWork mixed centeredVector
      replaceCentered =
        cong
          (λ centeredWork →
            common * Work.coherentWork mixed mixed
              + halfNu * centeredWork)
          centered

      rowSplit =
        trans row
          (trans weightedWork
            (trans split
              (trans replaceSelf replaceCentered)))
    in
    trans
      (solve
        ( halfNu
        ∷ Work.coherentWork mixed centeredVector
        ∷ common
        ∷ Work.coherentWork mixed mixed
        ∷ []))
      (cong
        (λ rowValue →
          rowValue - common * Work.coherentWork mixed mixed)
        (sym rowSplit))

  centeredR290DynamicNormalForm :
    (cutoff : Nat) (output : Z3.FourierMode) →
    let
      items = itemsAt cutoff output
      pairs = Bridge.Enum.allR290Pairs items
      mixed = mixedAt cutoff output
      centeredVector = centeredVectorAt cutoff output
      common = OutputRate.outputHeatRate nu I output
    in
    OutputRate.halfViscosity nu
      * Work.coherentWork mixed centeredVector
    ≡
      Row.rateDiagonalGram rate value items
      + R290Bridge.sumNonlinearRemainder pairs
      - R290Bridge.sumGramTangent pairs
      - common * Work.coherentWork mixed mixed
  centeredR290DynamicNormalForm cutoff output =
    let
      items = itemsAt cutoff output
      pairs = Bridge.Enum.allR290Pairs items
      mixed = mixedAt cutoff output
      common = OutputRate.outputHeatRate nu I output
      off =
        Bridge.literalOffDiagonalRateGramIsR290RemainderMinusTangent items
    in
    trans
      (centeredRowIdentity cutoff output)
      (trans
        (cong
          (λ offDiagonal →
            Row.rateDiagonalGram rate value items
              + offDiagonal
              - common * Work.coherentWork mixed mixed)
          off)
        (solve
          ( Row.rateDiagonalGram rate value items
          ∷ R290Bridge.sumNonlinearRemainder pairs
          ∷ R290Bridge.sumGramTangent pairs
          ∷ common
          ∷ Work.coherentWork mixed mixed
          ∷ [])))

------------------------------------------------------------------------
-- Trust boundary.
------------------------------------------------------------------------

centeredCovarianceR290DynamicNormalFormClosed : Bool
centeredCovarianceR290DynamicNormalFormClosed = true

r229AndR290ShareLiteralDoubleMixedPairCarrier : Bool
r229AndR290ShareLiteralDoubleMixedPairCarrier = true

centeredCovarianceEqualsUnweightedR503GramDebt : Bool
centeredCovarianceEqualsUnweightedR503GramDebt = false

remainingDifferenceIsPhysicalPairRateWeight : Bool
remainingDifferenceIsPhysicalPairRateWeight = true

newAnalyticEstimateIntroduced : Bool
newAnalyticEstimateIntroduced = false

clayPromotion : Bool
clayPromotion = false

centeredCovarianceR290DynamicNormalFormClosedIsTrue :
  centeredCovarianceR290DynamicNormalFormClosed ≡ true
centeredCovarianceR290DynamicNormalFormClosedIsTrue = refl

r229AndR290ShareLiteralDoubleMixedPairCarrierIsTrue :
  r229AndR290ShareLiteralDoubleMixedPairCarrier ≡ true
r229AndR290ShareLiteralDoubleMixedPairCarrierIsTrue = refl

centeredCovarianceEqualsUnweightedR503GramDebtIsFalse :
  centeredCovarianceEqualsUnweightedR503GramDebt ≡ false
centeredCovarianceEqualsUnweightedR503GramDebtIsFalse = refl

remainingDifferenceIsPhysicalPairRateWeightIsTrue :
  remainingDifferenceIsPhysicalPairRateWeight ≡ true
remainingDifferenceIsPhysicalPairRateWeightIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
