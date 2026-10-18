{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelectedSelfHelicitySplitRound721Exact where

------------------------------------------------------------------------
-- ROUND721 / LIVE R720 SELF SCALAR = HOMOCHIRAL + HETEROCHIRAL WORK
--
-- R720 puts the literal zero-safe selected-self fold on R625:
--
--   MultSelf_k = 2 C_k^self.
--
-- R632 already splits that SAME unit-weight exhaustive multiplier cell into
--
--   homochiral radial-increment + heterochiral literal radial-sum.
--
-- Lift that pointwise split through the complete output fibre and the exact
-- coherent-work consumer.  Division-free:
--
--   2 W(M_k,C_k^self)
--     = W(M_k,H_k) + W(M_k,E_k).
--
-- Thus an exact same-k cancellation, if it exists, must be an interaction
-- between these two resolved helicity channels.  There is no longer an opaque
-- selected-self commutator vector hiding the question.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNSelfHomochiralHeterochiralSplitRound632Exact as R632
import DASHI.Physics.Closure.NSTriadKNR571HeterochiralRadialSumSpecializationRound635Exact as R635
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650SelectedSelfMultiplierFoldRound720Exact as R720

module SelectedSelfHelicitySplit
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
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (velocityReality :
      Reality.RealityCondition
        (Audit.velocity (Field30.finiteSystem physicalSystem))) where

  module Prev =
    R720.SelectedSelfMultiplierFold
      physicalSystem S L H velocityTransverse velocityReality
  module Out = Prev.Out

  system = Field30.finiteSystem physicalSystem
  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem

  module Split =
    R632.SelfHelicitySplit632
      R694.unitWeight S L H system velocityTransverse

  module Hetero =
    R635.AttachToR632
      R694.unitWeight S L H system velocityTransverse

  homochiralCell heterochiralCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 R694.F
  homochiralCell = Split.homochiralExhaustive
  heterochiralCell = Split.heterochiralExhaustive

  homochiralFold heterochiralFold :
    Z3.FourierMode → C3.Complex3 R694.F
  homochiralFold output =
    R224.foldVector homochiralCell (Out.fibre output)
  heterochiralFold output =
    R224.foldVector heterochiralCell (Out.fibre output)

  multiplierFoldSplits :
    (output : Z3.FourierMode) →
    Prev.multiplierFold output
    ≡ C3.complex3Add
        (homochiralFold output)
        (heterochiralFold output)
  multiplierFoldSplits output =
    trans
      (Prev.foldPointwiseEqual
        Prev.multiplierCell
        (λ tau →
          C3.complex3Add (homochiralCell tau) (heterochiralCell tau))
        Split.selfMultiplierExhaustiveSplits
        (Out.fibre output))
      (R225.foldPointwiseAdd
        homochiralCell heterochiralCell (Out.fibre output))

  homochiralWork heterochiralWork :
    Z3.FourierMode → ℚ
  homochiralWork output =
    Work.coherentWork (Out.mixedFold output) (homochiralFold output)
  heterochiralWork output =
    Work.coherentWork (Out.mixedFold output) (heterochiralFold output)

  doubleSelfWorkIsHelicitySplit :
    (output : Z3.FourierMode) →
    Work.coherentWork (Out.mixedFold output) (Out.selfFold output)
      + Work.coherentWork (Out.mixedFold output) (Out.selfFold output)
    ≡ homochiralWork output + heterochiralWork output
  doubleSelfWorkIsHelicitySplit output =
    trans
      (sym (Prev.multiplierWorkIsDoubleSelfWork output))
      (trans
        (cong
          (Work.coherentWork (Out.mixedFold output))
          (multiplierFoldSplits output))
        (Work.workAddRight
          (Out.mixedFold output)
          (homochiralFold output)
          (heterochiralFold output)))

------------------------------------------------------------------------
-- Existing exact radial geometry attached to the two resolved channels.
------------------------------------------------------------------------

  homochiralCellUsesR632RadialIncrementCarrier : Bool
  homochiralCellUsesR632RadialIncrementCarrier =
    R632.round632HomochiralR571RadialCarrierWeldReused

  heterochiralVectorUsesLiteralRadialSumCarrier : Bool
  heterochiralVectorUsesLiteralRadialSumCarrier =
    R635.round635R632HeterochiralVectorRadialSumWeldClosed

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round721SelectedSelfMultiplierFoldHelicitySplitClosed : Bool
round721SelectedSelfMultiplierFoldHelicitySplitClosed = true

round721DoubleSelectedSelfWorkIsHomochiralPlusHeterochiral : Bool
round721DoubleSelectedSelfWorkIsHomochiralPlusHeterochiral = true

round721HomochiralChannelOnRadialIncrementCarrier : Bool
round721HomochiralChannelOnRadialIncrementCarrier = true

round721HeterochiralChannelOnRadialSumCarrier : Bool
round721HeterochiralChannelOnRadialSumCarrier = true

round721InternalSameKCancellationClosed : Bool
round721InternalSameKCancellationClosed = false

round721IntroducesEstimate : Bool
round721IntroducesEstimate = false

round721ClayPromotion : Bool
round721ClayPromotion = false

round721SelectedSelfMultiplierFoldHelicitySplitClosedIsTrue :
  round721SelectedSelfMultiplierFoldHelicitySplitClosed ≡ true
round721SelectedSelfMultiplierFoldHelicitySplitClosedIsTrue = refl

round721DoubleSelectedSelfWorkIsHomochiralPlusHeterochiralIsTrue :
  round721DoubleSelectedSelfWorkIsHomochiralPlusHeterochiral ≡ true
round721DoubleSelectedSelfWorkIsHomochiralPlusHeterochiralIsTrue = refl

round721InternalSameKCancellationClosedIsFalse :
  round721InternalSameKCancellationClosed ≡ false
round721InternalSameKCancellationClosedIsFalse = refl

round721IntroducesEstimateIsFalse :
  round721IntroducesEstimate ≡ false
round721IntroducesEstimateIsFalse = refl

round721ClayPromotionIsFalse :
  round721ClayPromotion ≡ false
round721ClayPromotionIsFalse = refl
