{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SingleSelfOutputPairingCollapseRound717Exact where

------------------------------------------------------------------------
-- ROUND717 / GLOBAL MASKED SELF ROW SUM -> ONE COHERENT PAIRING PER OUTPUT
--
-- R716 leaves exactly
--
--   S_N = sum_beta maskedSingleOuterRow(beta).
--
-- Each beta-row is itself a complete same-output spectator sum
--
--   sum_{alpha in F_k} W(M_alpha,C_beta).
--
-- Bilinearity of the real-Hermitian work therefore gives, on one literal
-- output fibre F_k,
--
--   sum_{beta in F_k} sum_{alpha in F_k} W(M_alpha,C_beta)
--     = W(sum_alpha M_alpha, sum_beta C_beta).
--
-- The k=0 mask is constant on the whole fibre.  R39's literal output-fibre
-- partition then regroups the COMPLETE physical enumeration without any
-- cardinality factor:
--
--   S_N = sum_{k in cutoffModes N, k != 0} W(M_k,C_k^self).
--
-- This is the natural exact carrier for the remaining self-cancellation test.
-- No sign, cancellation, estimate, norm, or Clay promotion is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650SingleSelfCompleteOrbitCollapseRound716Exact as R716

module OutputPairingCollapse
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R694.F)
    (S : Helical.HelicalModeScalars R694.F)
    (L : Helical.PeriodicHelicalProjectorLaws R694.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Collapse =
    R716.CompleteCollapse physicalSystem S L H velocityTransverse

  module One = Collapse.One

  cutoff = One.Carrier.Split.Full.Nested.Base.cutoff

  mixedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 R694.F
  mixedCell = One.Carrier.Split.Full.Nested.Base.mixedCell

  selfCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 R694.F
  selfCell = One.singleSelfCommutator

  fibre : Z3.FourierMode → List Physical.PhysicalTriadIncidence
  fibre output = Output.physicalOutputFiber cutoff output

  mixedFold selfFold :
    Z3.FourierMode → C3.Complex3 R694.F
  mixedFold output = R224.foldVector mixedCell (fibre output)
  selfFold output = R224.foldVector selfCell (fibre output)

  fixedOutputSelfPairing : Z3.FourierMode → ℚ
  fixedOutputSelfPairing output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = Work.coherentWork (mixedFold output) (selfFold output)

  spectatorRowFactorsLeft :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R546.spectatorRow One.singlePair beta items
    ≡ Work.coherentWork (R224.foldVector mixedCell items) (selfCell beta)
  spectatorRowFactorsLeft beta [] =
    sym (R597.workZeroLeft (selfCell beta))
  spectatorRowFactorsLeft beta (alpha ∷ rest) =
    trans
      (cong
        (One.singlePair alpha beta +_)
        (spectatorRowFactorsLeft beta rest))
      (sym
        (R597.workAddLeft
          (mixedCell alpha)
          (R224.foldVector mixedCell rest)
          (selfCell beta)))

  fixedOutputDoubleRowCollapse :
    (output : Z3.FourierMode) →
    R38.foldPower
      (λ beta → R546.spectatorRow One.singlePair beta (fibre output))
      (fibre output)
    ≡ Work.coherentWork (mixedFold output) (selfFold output)
  fixedOutputDoubleRowCollapse output =
    go (fibre output)
    where
    M = mixedFold output

    go :
      (items : List Physical.PhysicalTriadIncidence) →
      R38.foldPower
        (λ beta → R546.spectatorRow One.singlePair beta (fibre output))
        items
      ≡ Work.coherentWork M (R224.foldVector selfCell items)
    go [] =
      sym (R597.workZeroRight M)
    go (beta ∷ rest) =
      trans
        (cong₂ _+_
          (spectatorRowFactorsLeft beta (fibre output))
          (go rest))
        (sym
          (Work.workAddRight
            M (selfCell beta) (R224.foldVector selfCell rest)))

  actualMaskedRowOnOutput :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    beta ∈ fibre output →
    One.maskedSingleOuterRow beta
    ≡
    (case Output.modeEqual output Z3.zeroMode of λ where
      true → 0ℚ
      false → R546.spectatorRow One.singlePair beta (fibre output))
  actualMaskedRowOnOutput output beta member
    rewrite Output.physicalOutputFiberSound member = refl

  foldCongruentOnMembers :
    (left right : Physical.PhysicalTriadIncidence → ℚ) →
    (items : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) → beta ∈ items → left beta ≡ right beta) →
    R38.foldPower left items ≡ R38.foldPower right items
  foldCongruentOnMembers left right [] pointwise = refl
  foldCongruentOnMembers left right (beta ∷ rest) pointwise =
    cong₂ _+_
      (pointwise beta (here refl))
      (foldCongruentOnMembers left right rest
        (λ selected member → pointwise selected (there member)))

  foldZero :
    (items : List Physical.PhysicalTriadIncidence) →
    R38.foldPower (λ _ → 0ℚ) items ≡ 0ℚ
  foldZero [] = refl
  foldZero (_ ∷ rest) = foldZero rest

  maskedRowsOnOutputCollapse :
    (output : Z3.FourierMode) →
    R38.foldPower One.maskedSingleOuterRow (fibre output)
    ≡ fixedOutputSelfPairing output
  maskedRowsOnOutputCollapse output
    with Output.modeEqual output Z3.zeroMode
  ... | true =
    trans
      (foldCongruentOnMembers
        One.maskedSingleOuterRow
        (λ _ → 0ℚ)
        (fibre output)
        (λ beta member → actualMaskedRowOnOutput output beta member))
      (foldZero (fibre output))
  ... | false =
    trans
      (foldCongruentOnMembers
        One.maskedSingleOuterRow
        (λ beta → R546.spectatorRow One.singlePair beta (fibre output))
        (fibre output)
        (λ beta member → actualMaskedRowOnOutput output beta member))
      (fixedOutputDoubleRowCollapse output)

  outputIndexedSelfSum : List Z3.FourierMode → ℚ
  outputIndexedSelfSum [] = 0ℚ
  outputIndexedSelfSum (output ∷ rest) =
    fixedOutputSelfPairing output + outputIndexedSelfSum rest

  outputIndexedSelfSumIsConcatFold :
    (outputs : List Z3.FourierMode) →
    outputIndexedSelfSum outputs
    ≡ R38.foldPower One.maskedSingleOuterRow
        (R39.concatOutputFibers cutoff outputs)
  outputIndexedSelfSumIsConcatFold [] = refl
  outputIndexedSelfSumIsConcatFold (output ∷ rest) =
    trans
      (cong₂ _+_
        (sym (maskedRowsOnOutputCollapse output))
        (outputIndexedSelfSumIsConcatFold rest))
      (sym
        (R39.foldAppend
          One.maskedSingleOuterRow
          (fibre output)
          (R39.concatOutputFibers cutoff rest)))

  completeMaskedSelfRowsAreOutputPairings :
    Collapse.foldMaskedSingleRows
    ≡ outputIndexedSelfSum (Cube.cutoffModes cutoff)
  completeMaskedSelfRowsAreOutputPairings =
    trans
      (sym
        (R38.foldPermutationInvariant
          One.maskedSingleOuterRow
          (R39.literalOutputPartitionPermutation cutoff)))
      (sym
        (outputIndexedSelfSumIsConcatFold
          (Cube.cutoffModes cutoff)))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round717EachOutputDoubleRowCollapsesToOneCoherentPairing : Bool
round717EachOutputDoubleRowCollapsesToOneCoherentPairing = true

round717GlobalMaskedSelfSumRegroupedByLiteralOutputs : Bool
round717GlobalMaskedSelfSumRegroupedByLiteralOutputs = true

round717RemainingSelfQuestionIsOutputIndexedCoherentPairingSum : Bool
round717RemainingSelfQuestionIsOutputIndexedCoherentPairingSum = true

round717IntroducesEstimate : Bool
round717IntroducesEstimate = false

round717SelfCancellationClosed : Bool
round717SelfCancellationClosed = false

round717ClayPromotion : Bool
round717ClayPromotion = false

round717EachOutputDoubleRowCollapsesToOneCoherentPairingIsTrue :
  round717EachOutputDoubleRowCollapsesToOneCoherentPairing ≡ true
round717EachOutputDoubleRowCollapsesToOneCoherentPairingIsTrue = refl

round717GlobalMaskedSelfSumRegroupedByLiteralOutputsIsTrue :
  round717GlobalMaskedSelfSumRegroupedByLiteralOutputs ≡ true
round717GlobalMaskedSelfSumRegroupedByLiteralOutputsIsTrue = refl

round717RemainingSelfQuestionIsOutputIndexedCoherentPairingSumIsTrue :
  round717RemainingSelfQuestionIsOutputIndexedCoherentPairingSum ≡ true
round717RemainingSelfQuestionIsOutputIndexedCoherentPairingSumIsTrue = refl

round717IntroducesEstimateIsFalse :
  round717IntroducesEstimate ≡ false
round717IntroducesEstimateIsFalse = refl

round717SelfCancellationClosedIsFalse :
  round717SelfCancellationClosed ≡ false
round717SelfCancellationClosedIsFalse = refl

round717ClayPromotionIsFalse :
  round717ClayPromotion ≡ false
round717ClayPromotionIsFalse = refl
