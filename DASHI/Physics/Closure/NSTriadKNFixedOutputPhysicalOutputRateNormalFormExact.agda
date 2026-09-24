module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalOutputRateNormalFormExact where

------------------------------------------------------------------------
-- FIXED-OUTPUT PHYSICAL RATE NORMAL FORM -- NO FIBRE MEAN
--
-- On p+q=k,
--
--   |p|^2 + |q|^2 = (|k|^2 + |p-q|^2)/2.
--
-- Hence the literal viscous cell rate splits EXACTLY as
--
--   lambda_pq
--     = (nu/2)|k|^2 + (nu/2)|p-q|^2.
--
-- The previous arithmetic-mean covariance representation is correct, but it is
-- not the least-privilege dynamic coordinate: its division-free form carries a
-- factor equal to the fibre cardinality.  Here we instead choose the physical
-- output heat rate
--
--   lambda_k = (nu/2)|k|^2
--
-- as the common rate in the already-proved coherent-work decomposition.
--
-- Therefore, on the literal fixed-output fibre,
--
--   W(M, decay + lambda_k M)
--     = -(nu/2) W(M, sum_{p+q=k}|p-q|^2 A_pq),
--
-- and consequently
--
--   W(M, commutator)
--     = W(M, tangent)
--       + lambda_k W(M,M)
--       + (nu/2) W(M, sum |p-q|^2 A_pq).
--
-- No finite-fibre average, division by cardinality, complete-graph expansion,
-- absolute value, norm majorant, or cutoff factor appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector

F : C3.RealField _
F = Rational.rationalRealField

half : ℚ
half = + 1 / 2

halfViscosity : ℚ → ℚ
halfViscosity nu = half * nu

outputHeatRate :
  ∀ {E : C3.IntegerEmbedding F} →
  ℚ → C3.ModeInverseSquare F E → Z3.FourierMode → ℚ
outputHeatRate nu I output =
  halfViscosity nu * C3.normSquared I output

centeredCellRate :
  (E : C3.IntegerEmbedding F) →
  ℚ → Physical.PhysicalTriadIncidence → ℚ
centeredCellRate E nu tau =
  halfViscosity nu
    * Rate.centeredSquare E (Physical.p tau) (Physical.q tau)

cellRateSplitsAtPhysicalOutput :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (output : Z3.FourierMode) →
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ output →
  Cov.cellRate (Centered.modalViscousRate nu I) tau
  ≡ outputHeatRate nu I output + centeredCellRate E nu tau
cellRateSplitsAtPhysicalOutput E I nu output tau sameOutput =
  let
    p = Physical.p tau
    q = Physical.q tau
    S = Rate.inputSquareMass I p q
    Ktau = C3.normSquared I (Physical.k tau)
    K = C3.normSquared I output
    C = Rate.centeredSquare E p q

    halfParallelogram :
      S ≡ half * (Ktau + C)
    halfParallelogram =
      trans
        (solve (S ∷ []))
        (cong (half *_) (Rate.incidenceParallelogram E I tau))

    outputMeaning : Ktau ≡ K
    outputMeaning = cong (C3.normSquared I) sameOutput

    inputMassMeaning :
      S ≡ half * (K + C)
    inputMassMeaning =
      trans halfParallelogram
        (cong (λ square → half * (square + C)) outputMeaning)

    physicalRateMeaning :
      Cov.cellRate (Centered.modalViscousRate nu I) tau
      ≡ nu * S
    physicalRateMeaning =
      trans
        (Centered.cellRateMeaning nu I tau)
        refl
  in
  trans physicalRateMeaning
    (trans
      (cong (nu *_) inputMassMeaning)
      (solve (nu ∷ K ∷ C ∷ [])))

weightedRateWorkSplitsAtPhysicalOutput :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (items : List Physical.PhysicalTriadIncidence) →
  Centered.OutputHomogeneous output items →
  Cov.weightedWorkSum
      (Cov.cellRate (Centered.modalViscousRate nu I)) work items
  ≡
    outputHeatRate nu I output * Cov.workSum work items
    + halfViscosity nu *
        Cov.weightedWorkSum
          (Vector.centeredFrequencyMultiplier E) work items
weightedRateWorkSplitsAtPhysicalOutput E I nu work [] homogeneous =
  solve []
weightedRateWorkSplitsAtPhysicalOutput
    E I nu work {output} (tau ∷ rest) homogeneous =
  let
    rate = Cov.cellRate (Centered.modalViscousRate nu I) tau
    common = outputHeatRate nu I output
    centered = Vector.centeredFrequencyMultiplier E tau
    headWork = work tau
    tailWork = Cov.workSum work rest
    tailWeightedRate =
      Cov.weightedWorkSum
        (Cov.cellRate (Centered.modalViscousRate nu I)) work rest
    tailWeightedCentered =
      Cov.weightedWorkSum
        (Vector.centeredFrequencyMultiplier E) work rest

    headRate :
      rate ≡ common + halfViscosity nu * centered
    headRate =
      cellRateSplitsAtPhysicalOutput E I nu output tau
        (Centered.headOutput homogeneous)

    tail :
      tailWeightedRate
      ≡ common * tailWork + halfViscosity nu * tailWeightedCentered
    tail =
      weightedRateWorkSplitsAtPhysicalOutput
        E I nu work rest (Centered.tailHomogeneous homogeneous)
  in
  trans
    (cong
      (λ selectedRate → selectedRate * headWork + tailWeightedRate)
      headRate)
    (trans
      (cong
        ((common + halfViscosity nu * centered) * headWork +_)
        tail)
      (solve
        ( common ∷ halfViscosity nu ∷ centered ∷ headWork
        ∷ tailWork ∷ tailWeightedCentered ∷ [])))

literalWeightedRateWorkSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  Cov.weightedWorkSum
      (Cov.cellRate (Centered.modalViscousRate nu I)) work
      (Output.physicalOutputFiber cutoff output)
  ≡
    outputHeatRate nu I output *
      Cov.workSum work (Output.physicalOutputFiber cutoff output)
    + halfViscosity nu *
        Cov.weightedWorkSum
          (Vector.centeredFrequencyMultiplier E) work
          (Output.physicalOutputFiber cutoff output)
literalWeightedRateWorkSplit E I nu work cutoff output =
  weightedRateWorkSplitsAtPhysicalOutput E I nu work
    (Output.physicalOutputFiber cutoff output)
    (Centered.literalOutputFibreHomogeneous cutoff output)

literalPhysicalOutputRateResidualWork :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    decay =
      R224.foldVector
        (D1a.variableDecayCell
          (Centered.modalViscousRate nu I) S velocity)
        items
    residual =
      Work.coherentCovarianceResidual
        (outputHeatRate nu I output) mixed decay
    centeredVector =
      Vector.weightedVectorSum
        (Vector.centeredFrequencyMultiplier E) value items
  in
  Work.coherentWork mixed residual
  ≡
  0ℚ - halfViscosity nu * Work.coherentWork mixed centeredVector
literalPhysicalOutputRateResidualWork
    E I nu S velocity cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rho = Centered.modalViscousRate nu I
    rate = Cov.cellRate rho
    work = Cov.cellWork mixed value
    decay = R224.foldVector (D1a.variableDecayCell rho S velocity) items
    common = outputHeatRate nu I output
    centeredRate = Vector.centeredFrequencyMultiplier E
    centeredVector = Vector.weightedVectorSum centeredRate value items

    residualSplit :
      Work.coherentWork mixed
        (Work.coherentCovarianceResidual common mixed decay)
      ≡ Work.coherentWork mixed decay
        + common * Work.coherentWork mixed mixed
    residualSplit =
      Work.coherentResidualWorkSplit common mixed decay

    decayMeaning :
      Work.coherentWork mixed decay
      ≡ 0ℚ - Cov.weightedWorkSum rate work items
    decayMeaning =
      Cov.variableDecayWorkSum mixed rho S velocity items

    selfMeaning :
      Work.coherentWork mixed mixed ≡ Cov.workSum work items
    selfMeaning =
      sym (Cov.workSumAgainstFold mixed value items)

    rateSplit :
      Cov.weightedWorkSum rate work items
      ≡ common * Cov.workSum work items
        + halfViscosity nu *
            Cov.weightedWorkSum centeredRate work items
    rateSplit =
      literalWeightedRateWorkSplit E I nu work cutoff output

    centeredWorkMeaning :
      Work.coherentWork mixed centeredVector
      ≡ Cov.weightedWorkSum centeredRate work items
    centeredWorkMeaning =
      Vector.weightedVectorWorkMeaning mixed centeredRate value items
  in
  trans residualSplit
    (trans
      (cong₂ _+_
        decayMeaning
        (cong (common *_) selfMeaning))
      (trans
        (cong
          (λ weighted →
            (0ℚ - weighted)
              + common * Cov.workSum work items)
          rateSplit)
        (trans
          (solve
            ( common
            ∷ Cov.workSum work items
            ∷ halfViscosity nu
            ∷ Cov.weightedWorkSum centeredRate work items
            ∷ []))
          (cong
            (λ centeredWork →
              0ℚ - halfViscosity nu * centeredWork)
            (sym centeredWorkMeaning)))))

literalFixedOutputCommutatorPhysicalRateNormalForm :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  let
    rho = Centered.modalViscousRate nu I
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    tangent = Work.fixedOutputDampedTangent rho S velocity forcing cutoff output
    commutator = Work.fixedOutputCommutator S velocity forcing cutoff output
    centeredVector =
      Vector.weightedVectorSum
        (Vector.centeredFrequencyMultiplier E) value items
    common = outputHeatRate nu I output
  in
  Work.coherentWork mixed commutator
  ≡
    Work.coherentWork mixed tangent
    + common * Work.coherentWork mixed mixed
    + halfViscosity nu * Work.coherentWork mixed centeredVector
literalFixedOutputCommutatorPhysicalRateNormalForm
    E I nu S velocity forcing cutoff output =
  let
    rho = Centered.modalViscousRate nu I
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    tangent = Work.fixedOutputDampedTangent rho S velocity forcing cutoff output
    commutator = Work.fixedOutputCommutator S velocity forcing cutoff output
    decay = Work.fixedOutputVariableDecay rho S velocity cutoff output
    common = outputHeatRate nu I output
    residual = Work.coherentCovarianceResidual common mixed decay
    centeredVector =
      Vector.weightedVectorSum
        (Vector.centeredFrequencyMultiplier E) value items

    base :
      Work.coherentWork mixed commutator
      ≡ Work.coherentWork mixed tangent
          + common * Work.coherentWork mixed mixed
          - Work.coherentWork mixed residual
    base =
      Work.fixedOutputCommutatorWorkIsEndpointRateMinusCovariance
        common rho S velocity forcing cutoff output

    residualMeaning :
      Work.coherentWork mixed residual
      ≡ 0ℚ - halfViscosity nu * Work.coherentWork mixed centeredVector
    residualMeaning =
      literalPhysicalOutputRateResidualWork
        E I nu S velocity cutoff output
  in
  trans base
    (trans
      (cong
        (λ residualWork →
          Work.coherentWork mixed tangent
            + common * Work.coherentWork mixed mixed
            - residualWork)
        residualMeaning)
      (solve
        ( Work.coherentWork mixed tangent
        ∷ common
        ∷ Work.coherentWork mixed mixed
        ∷ halfViscosity nu
        ∷ Work.coherentWork mixed centeredVector
        ∷ [])))

physicalOutputRateNormalFormClosed : Bool
physicalOutputRateNormalFormClosed = true

physicalOutputRateNormalFormUsesFibreMean : Bool
physicalOutputRateNormalFormUsesFibreMean = false

physicalOutputRateNormalFormUsesCardinality : Bool
physicalOutputRateNormalFormUsesCardinality = false

physicalOutputRateNormalFormUsesAbsoluteValue : Bool
physicalOutputRateNormalFormUsesAbsoluteValue = false

remainingAnalyticLeafIsCenteredMultiplierConvolutionWork : Bool
remainingAnalyticLeafIsCenteredMultiplierConvolutionWork = true

clayPromotion : Bool
clayPromotion = false

physicalOutputRateNormalFormClosedIsTrue :
  physicalOutputRateNormalFormClosed ≡ true
physicalOutputRateNormalFormClosedIsTrue = refl

physicalOutputRateNormalFormUsesFibreMeanIsFalse :
  physicalOutputRateNormalFormUsesFibreMean ≡ false
physicalOutputRateNormalFormUsesFibreMeanIsFalse = refl

physicalOutputRateNormalFormUsesCardinalityIsFalse :
  physicalOutputRateNormalFormUsesCardinality ≡ false
physicalOutputRateNormalFormUsesCardinalityIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
