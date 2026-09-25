{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelfExternalRecombinationRound722Exact where

------------------------------------------------------------------------
-- ROUND722 / RETIRE SEPARATE SELF CANCELLATION: RECOMBINE ON THE EXACT
--            COMPLETE NESTED ORBIT
--
-- R708 already proves, on the literal R700 carrier,
--
--   CompleteNestedOrbit = CompleteSelfOrbit + CompleteExternalOrbit.
--
-- R700 proves independently
--
--   CompleteNestedOrbit = 12 * GlobalCommutator.
--
-- R714-R717 now identify the self term itself:
--
--   CompleteSelfOrbit
--     = 4 * CompleteSingleSelfOrbit
--     = 4 * (3 * CompleteMaskedSelfRows)
--     = 12 * OutputIndexedSelfSum.
--
-- Therefore, without assuming Self=0 and without touching the p=0 branch,
--
--   12 * GlobalCommutator
--     = 12 * OutputIndexedSelfSum + CompleteExternalOrbit.
--
-- This is the decisive routing theorem: self and external are NOT separate
-- analytic obligations on this max-cut.  Their exact signed combination is
-- already the single live global commutator currency consumed downstream.
--
-- R720/R721 remain useful diagnostics for the internal self geometry, but
-- cancellation of that channel is no longer required before proceeding to the
-- cutoff-uniform signed spacetime estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as A3
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650UnitNestedOrbitSelfExternalSplitRound708Exact as R708
import DASHI.Physics.Closure.NSTriadKNR650SingleSelfCommutatorOrbitRound714Exact as R714
import DASHI.Physics.Closure.NSTriadKNR650SingleSelfCompleteOrbitCollapseRound716Exact as R716
import DASHI.Physics.Closure.NSTriadKNR650SingleSelfOutputPairingCollapseRound717Exact as R717

module Recombine
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

  module Split =
    R708.UnitOrbitSplit physicalSystem S L H velocityTransverse
  module One =
    R714.SingleSelfOrbit physicalSystem S L H velocityTransverse
  module Collapse =
    R716.CompleteCollapse physicalSystem S L H velocityTransverse
  module Pairing =
    R717.OutputPairingCollapse physicalSystem S L H velocityTransverse

  items =
    Physical.physicalTriadEnumeration
      Split.Full.Nested.Base.cutoff

  selfOutputSum : ℚ
  selfOutputSum =
    Pairing.outputIndexedSelfSum
      (Cube.cutoffModes
        Split.Full.Nested.Base.cutoff)

  completeExternalOrbit : ℚ
  completeExternalOrbit =
    Split.foldExternalOrbit items

  globalCommutator : ℚ
  globalCommutator =
    Split.Full.Nested.Base.nonzeroGlobalCommutatorWork

  completeSelfOrbitIsTwelveOutputPairings :
    Split.foldSelfOrbit items
    ≡ R700.twelve * selfOutputSum
  completeSelfOrbitIsTwelveOutputPairings =
    trans
      One.completeSelfOrbitIsFourSingleSelfCommutatorOrbit
      (trans
        (cong
          (A3.four *_)
          Collapse.completeSingleSelfOrbitIsThreeGlobalRows)
        (trans
          (cong
            (λ selected →
              A3.four * (R716.three * selected))
            Pairing.completeMaskedSelfRowsAreOutputPairings)
          (solve (selfOutputSum ∷ []))))

  combinedSelfExternalResidue : ℚ
  combinedSelfExternalResidue =
    R700.twelve * selfOutputSum + completeExternalOrbit

  combinedSelfExternalIsCompleteNestedOrbit :
    combinedSelfExternalResidue
    ≡
    R38.foldPower
      Split.Full.nestedTriadOrbitResidue items
  combinedSelfExternalIsCompleteNestedOrbit =
    trans
      (cong₂ _+_
        (sym completeSelfOrbitIsTwelveOutputPairings)
        refl)
      (sym Split.completeNestedOrbitSplitsSelfExternal)

  combinedSelfExternalIsTwelveGlobalCommutator :
    combinedSelfExternalResidue
    ≡ R700.twelve * globalCommutator
  combinedSelfExternalIsTwelveGlobalCommutator =
    trans
      (cong₂ _+_
        (sym completeSelfOrbitIsTwelveOutputPairings)
        refl)
      (trans
        (sym Split.completeNestedOrbitSplitsSelfExternal)
        Split.Full.completeNestedTriadOrbitResidueIsTwelveCoherentCommutator)

  twelveGlobalCommutatorIsCombinedSelfExternal :
    R700.twelve * globalCommutator
    ≡ combinedSelfExternalResidue
  twelveGlobalCommutatorIsCombinedSelfExternal =
    sym combinedSelfExternalIsTwelveGlobalCommutator

------------------------------------------------------------------------
-- Status / max-cut routing.
------------------------------------------------------------------------

round722CompleteSelfOrbitIsTwelveOutputPairings : Bool
round722CompleteSelfOrbitIsTwelveOutputPairings = true

round722SelfExternalRecombineToSingleGlobalCommutator : Bool
round722SelfExternalRecombineToSingleGlobalCommutator = true

round722CombinedSelfExternalIsLiteralCompleteNestedOrbit : Bool
round722CombinedSelfExternalIsLiteralCompleteNestedOrbit = true

round722SeparateSelfCancellationRequiredForMaxCut : Bool
round722SeparateSelfCancellationRequiredForMaxCut = false

round722SeparateExternalPaymentRequiredForMaxCut : Bool
round722SeparateExternalPaymentRequiredForMaxCut = false

round722RemainingAnalyticObjectIsCombinedGlobalCommutator : Bool
round722RemainingAnalyticObjectIsCombinedGlobalCommutator = true

round722IntroducesEstimate : Bool
round722IntroducesEstimate = false

round722ClayPromotion : Bool
round722ClayPromotion = false

round722CompleteSelfOrbitIsTwelveOutputPairingsIsTrue :
  round722CompleteSelfOrbitIsTwelveOutputPairings ≡ true
round722CompleteSelfOrbitIsTwelveOutputPairingsIsTrue = refl

round722SelfExternalRecombineToSingleGlobalCommutatorIsTrue :
  round722SelfExternalRecombineToSingleGlobalCommutator ≡ true
round722SelfExternalRecombineToSingleGlobalCommutatorIsTrue = refl

round722SeparateSelfCancellationRequiredForMaxCutIsFalse :
  round722SeparateSelfCancellationRequiredForMaxCut ≡ false
round722SeparateSelfCancellationRequiredForMaxCutIsFalse = refl

round722SeparateExternalPaymentRequiredForMaxCutIsFalse :
  round722SeparateExternalPaymentRequiredForMaxCut ≡ false
round722SeparateExternalPaymentRequiredForMaxCutIsFalse = refl

round722RemainingAnalyticObjectIsCombinedGlobalCommutatorIsTrue :
  round722RemainingAnalyticObjectIsCombinedGlobalCommutator ≡ true
round722RemainingAnalyticObjectIsCombinedGlobalCommutatorIsTrue = refl

round722IntroducesEstimateIsFalse :
  round722IntroducesEstimate ≡ false
round722IntroducesEstimateIsFalse = refl

round722ClayPromotionIsFalse :
  round722ClayPromotion ≡ false
round722ClayPromotionIsFalse = refl
