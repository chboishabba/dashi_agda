module DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact where

------------------------------------------------------------------------
-- FIXED-OUTPUT COVARIANCE AS ONE CENTERED-MULTIPLIER VECTOR RESIDUAL
--
-- For a finite coherent family A_i, let
--
--   M   = sum_i A_i,
--   w_i = 2 Re <M,A_i>,
--   c_i = any scalar multiplier.
--
-- The division-free covariance owner already proves
--
--   sum_{i<j} (c_i-c_j)(w_i-w_j)
--     = n sum_i c_i w_i - (sum_i c_i)(sum_i w_i).
--
-- By exact Hermitian linearity this is not merely a scalar complete-graph
-- expression.  It is ONE coherent work:
--
--   = 2 Re < M ,
--       n sum_i c_i A_i - (sum_i c_i) M >.
--
-- Specializing c_i = |p_i-q_i|^2 on a literal fixed-output fibre therefore
-- turns the R229/Rd1b2 covariance into a single centered-frequency multiplier
-- residual.  No absolute value, pair count estimate, positivity observer, or
-- cutoff factor is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate

F : C3.RealField _
F = Rational.rationalRealField

weightedVectorSum :
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  C3.Complex3 F
weightedVectorSum multiplier value [] = C3.complex3Zero F
weightedVectorSum multiplier value (tau ∷ rest) =
  C3.complex3Add
    (R291.realScale (multiplier tau) (value tau))
    (weightedVectorSum multiplier value rest)

workZeroRight :
  (left : C3.Complex3 F) →
  Work.coherentWork left (C3.complex3Zero F) ≡ 0ℚ
workZeroRight left =
  trans
    (cong (Work.two *_) (R383.realCrossZeroRight left))
    (solve [])

weightedVectorWorkMeaning :
  (mixed : C3.Complex3 F) →
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Work.coherentWork mixed (weightedVectorSum multiplier value items)
  ≡ Cov.weightedWorkSum multiplier (Cov.cellWork mixed value) items
weightedVectorWorkMeaning mixed multiplier value [] =
  workZeroRight mixed
weightedVectorWorkMeaning mixed multiplier value (tau ∷ rest) =
  trans
    (Work.workAddRight mixed
      (R291.realScale (multiplier tau) (value tau))
      (weightedVectorSum multiplier value rest))
    (trans
      (cong₂ _+_
        (Work.workScaleRight (multiplier tau) mixed (value tau))
        (weightedVectorWorkMeaning mixed multiplier value rest))
      refl)

centeredMultiplierResidual :
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  C3.Complex3 F
centeredMultiplierResidual multiplier value items =
  let
    mixed = R224.foldVector value items
    weighted = weightedVectorSum multiplier value items
    n = Cov.natAsRational (length items)
    totalMultiplier = Cov.rateSum multiplier items
  in
  C3.complex3Add
    (R291.realScale n weighted)
    (R291.realScale (0ℚ - totalMultiplier) mixed)

pairDifferenceIsCenteredMultiplierWork :
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  let
    mixed = R224.foldVector value items
    work = Cov.cellWork mixed value
  in
  Cov.pairDifferenceWorkSum multiplier work items
  ≡ Work.coherentWork mixed
      (centeredMultiplierResidual multiplier value items)
pairDifferenceIsCenteredMultiplierWork multiplier value items =
  let
    mixed = R224.foldVector value items
    work = Cov.cellWork mixed value
    weighted = weightedVectorSum multiplier value items
    n = Cov.natAsRational (length items)
    totalMultiplier = Cov.rateSum multiplier items
    weightedScalar = Cov.weightedWorkSum multiplier work items
    totalWork = Cov.workSum work items

    closed :
      Cov.pairDifferenceWorkSum multiplier work items
      ≡ n * weightedScalar - totalMultiplier * totalWork
    closed = Cov.pairDifferenceClosedForm multiplier work items

    weightedMeaning :
      Work.coherentWork mixed weighted ≡ weightedScalar
    weightedMeaning =
      weightedVectorWorkMeaning mixed multiplier value items

    totalWorkMeaning :
      totalWork ≡ Work.coherentWork mixed mixed
    totalWorkMeaning =
      Cov.workSumAgainstFold mixed value items

    residualWork :
      Work.coherentWork mixed
        (centeredMultiplierResidual multiplier value items)
      ≡ n * weightedScalar
          - totalMultiplier * totalWork
    residualWork =
      trans
        (Work.workAddRight mixed
          (R291.realScale n weighted)
          (R291.realScale (0ℚ - totalMultiplier) mixed))
        (trans
          (cong₂ _+_
            (Work.workScaleRight n mixed weighted)
            (Work.workScaleRight (0ℚ - totalMultiplier) mixed mixed))
          (trans
            (cong₂ _+_
              (cong (n *_) weightedMeaning)
              (cong ((0ℚ - totalMultiplier) *_) (sym totalWorkMeaning)))
            (solve (n ∷ weightedScalar ∷ totalMultiplier ∷ totalWork ∷ []))))
  in
  trans closed (sym residualWork)

centeredFrequencyMultiplier :
  (E : C3.IntegerEmbedding F) →
  Physical.PhysicalTriadIncidence → ℚ
centeredFrequencyMultiplier E tau =
  Rate.centeredSquare E (Physical.p tau) (Physical.q tau)

literalFixedOutputCenteredMultiplierResidual :
  (E : C3.IntegerEmbedding F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Nat → Physical.PhysicalTriadIncidence → C3.Complex3 F
literalFixedOutputCenteredMultiplierResidual E value cutoff tau =
  centeredMultiplierResidual
    (centeredFrequencyMultiplier E)
    value
    (Output.physicalOutputFiber cutoff (Physical.k tau))

literalFixedOutputCenteredCovarianceIsOneVectorWork :
  (E : C3.IntegerEmbedding F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (cutoff : Nat) (output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    mixed = R224.foldVector value items
    multiplier = centeredFrequencyMultiplier E
    work = Cov.cellWork mixed value
  in
  Cov.pairDifferenceWorkSum multiplier work items
  ≡ Work.coherentWork mixed
      (centeredMultiplierResidual multiplier value items)
literalFixedOutputCenteredCovarianceIsOneVectorWork E value cutoff output =
  pairDifferenceIsCenteredMultiplierWork
    (centeredFrequencyMultiplier E)
    value
    (Output.physicalOutputFiber cutoff output)

centeredCovarianceCollapsedToOneVectorResidual : Bool
centeredCovarianceCollapsedToOneVectorResidual = true

centeredCovarianceVectorNormalFormUsesAbsoluteValue : Bool
centeredCovarianceVectorNormalFormUsesAbsoluteValue = false

centeredCovarianceVectorNormalFormAddsCutoffFactor : Bool
centeredCovarianceVectorNormalFormAddsCutoffFactor = false

quantitativeCenteredMultiplierResidualPaymentClosed : Bool
quantitativeCenteredMultiplierResidualPaymentClosed = false

clayPromotion : Bool
clayPromotion = false

centeredCovarianceCollapsedToOneVectorResidualIsTrue :
  centeredCovarianceCollapsedToOneVectorResidual ≡ true
centeredCovarianceCollapsedToOneVectorResidualIsTrue = refl

centeredCovarianceVectorNormalFormUsesAbsoluteValueIsFalse :
  centeredCovarianceVectorNormalFormUsesAbsoluteValue ≡ false
centeredCovarianceVectorNormalFormUsesAbsoluteValueIsFalse = refl

centeredCovarianceVectorNormalFormAddsCutoffFactorIsFalse :
  centeredCovarianceVectorNormalFormAddsCutoffFactor ≡ false
centeredCovarianceVectorNormalFormAddsCutoffFactorIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
