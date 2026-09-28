{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedExternalCommutatorRound807Exact where

------------------------------------------------------------------------
-- ROUND807 / MOVE THE SEPARATED EXTERNAL R230 WORK ONTO THE R670
--            SWAP-INVARIANT EXTERNAL COMMUTATOR CARRIER
--
-- R802 leaves the external part of the separated R230 currency as coherent
-- work against the fully-separated masked external PRODUCT-RULE fold.
--
-- R670 already proves the exact fixed-output identity
--
--   fold (W * ExternalProductRule)
--     = fold (W * ExternalCommutator)
--
-- for every swap-invariant R294 weight W.  R798 proves that the literal
-- fully-separated mask is exactly such a weight.
--
-- The R802 maskedExternalCell is pointwise the R670 weightedProductRule for
-- W = separatedWeight.  Therefore, output by output and globally,
--
--   External_sep
--     = coherent work against the literal separated R625/R670
--       external commutator fold.
--
-- This is representation only.  No norm, estimate, absolute value, helicity
-- row identification, or external-network payment is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650WeightedExternalProductRuleCommutatorRound670Exact as R670
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230WeightRound798Exact as R798
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230SelfExternalRound802Exact as R802

module SeparatedExternalCommutator
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R802.F)
    (S : Helical.HelicalModeScalars R802.F)
    (L : Helical.PeriodicHelicalProjectorLaws R802.F
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
    R802.SeparatedR230SelfExternal
      physicalSystem S L H velocityTransverse

  module Ext =
    R670.WeightedExternal
      physicalSystem S (R798.separatedWeight R802.F)

  cutoff = Split.cutoff

  weightedExternalProductIsMasked :
    (beta : Physical.PhysicalTriadIncidence) →
    Ext.weightedProductRule beta ≡ Split.maskedExternalCell beta
  weightedExternalProductIsMasked beta
    with R781.ccTouched beta
  ... | true =
    R106.complex3ScaleZeroScalar
      (Split.Net.externalProductRuleCell beta)
  ... | false =
    R106.complex3ScaleOne
      (Split.Net.externalProductRuleCell beta)

  externalCommutatorFold :
    Z3.FourierMode → C3.Complex3 R802.F
  externalCommutatorFold output =
    R224.foldVector Ext.weightedCommutator
      (Output.physicalOutputFiber cutoff output)

  externalProductFoldIsCommutatorFold :
    (output : Z3.FourierMode) →
    Split.externalFold output ≡ externalCommutatorFold output
  externalProductFoldIsCommutatorFold output =
    let
      fibre = Output.physicalOutputFiber cutoff output

      productMeaning :
        Split.externalFold output
        ≡ R224.foldVector Ext.weightedProductRule fibre
      productMeaning =
        Split.Net.foldCongruent
          Split.maskedExternalCell
          Ext.weightedProductRule
          (λ beta → 
            let eq = weightedExternalProductIsMasked beta in
            Relation.Binary.PropositionalEquality.sym eq)
          fibre
    in
    trans
      productMeaning
      (Ext.fixedOutputWeightedExternalProductRuleIsCommutator
        cutoff output)

  outputExternalCommutatorWork : Z3.FourierMode → ℚ
  outputExternalCommutatorWork output =
    Work.coherentWork
      (Split.Id.mixedFold output)
      (externalCommutatorFold output)

  selectedExternalCommutatorWork : Z3.FourierMode → ℚ
  selectedExternalCommutatorWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = outputExternalCommutatorWork output

  selectedExternalWorkIsCommutatorWork :
    (output : Z3.FourierMode) →
    Split.selectedExternalWork output
    ≡ selectedExternalCommutatorWork output
  selectedExternalWorkIsCommutatorWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = refl
  ... | false =
    cong
      (Work.coherentWork (Split.Id.mixedFold output))
      (externalProductFoldIsCommutatorFold output)

  sumExternalCommutatorWork : List Z3.FourierMode → ℚ
  sumExternalCommutatorWork [] = 0ℚ
  sumExternalCommutatorWork (output ∷ rest) =
    selectedExternalCommutatorWork output
      + sumExternalCommutatorWork rest

  globalExternalCommutatorWork : ℚ
  globalExternalCommutatorWork =
    sumExternalCommutatorWork (Cube.cutoffModes cutoff)

  globalExternalWorkIsCommutatorWork :
    Split.globalExternalWork ≡ globalExternalCommutatorWork
  globalExternalWorkIsCommutatorWork =
    go (Cube.cutoffModes cutoff)
    where
    go :
      (outputs : List Z3.FourierMode) →
      Split.sumExternalWork outputs
      ≡ sumExternalCommutatorWork outputs
    go [] = refl
    go (output ∷ rest) =
      cong₂ _+_
        (selectedExternalWorkIsCommutatorWork output)
        (go rest)

round807SeparatedExternalProductRuleToCommutatorClosed : Bool
round807SeparatedExternalProductRuleToCommutatorClosed = true

round807SeparatedExternalWorkOnR670Carrier : Bool
round807SeparatedExternalWorkOnR670Carrier = true

round807IntroducesEstimate : Bool
round807IntroducesEstimate = false

round807ExternalPaymentClosed : Bool
round807ExternalPaymentClosed = false

round807W2Closed : Bool
round807W2Closed = false

round807ClayPromotion : Bool
round807ClayPromotion = false

round807SeparatedExternalProductRuleToCommutatorClosedIsTrue :
  round807SeparatedExternalProductRuleToCommutatorClosed ≡ true
round807SeparatedExternalProductRuleToCommutatorClosedIsTrue = refl

round807SeparatedExternalWorkOnR670CarrierIsTrue :
  round807SeparatedExternalWorkOnR670Carrier ≡ true
round807SeparatedExternalWorkOnR670CarrierIsTrue = refl

round807IntroducesEstimateIsFalse :
  round807IntroducesEstimate ≡ false
round807IntroducesEstimateIsFalse = refl

round807ExternalPaymentClosedIsFalse :
  round807ExternalPaymentClosed ≡ false
round807ExternalPaymentClosedIsFalse = refl

round807W2ClosedIsFalse :
  round807W2Closed ≡ false
round807W2ClosedIsFalse = refl

round807ClayPromotionIsFalse :
  round807ClayPromotion ≡ false
round807ClayPromotionIsFalse = refl
