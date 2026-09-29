{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedR438FourHelicityRound812Exact where

------------------------------------------------------------------------
-- ROUND812 / THE R811 FULL SEPARATED COMPANION ON THE LITERAL R573
--            FOUR-HELICITY MULTIPLIER-DIFFERENCE CARRIER
--
-- R811 reduces the fully-separated residual to
--
--   D_sep = 2 (18 F_sep - Q_sep),
--
-- where F_sep is coherent work against R438's exhaustive separated forcing
-- companion.
--
-- R573 already proves for ANY R294 swap-invariant weight, pointwise and with
-- the p=0 branch totalised,
--
--   Companion438(tau) + Companion438(tau)
--     = NestedFourSign573(tau).
--
-- Specialising that theorem to R798's literal separated indicator therefore
-- preserves the physical mask BEFORE the inner expansion.  Folding over any
-- physical incidence list gives
--
--   NestedFold = 2 CompanionFold,
--
-- and coherent-work linearity gives
--
--   NestedWork = 2 CompanionWork.
--
-- The nested cell is not an abstract replacement.  Its forcing slot is the
-- complete inner output fibre at p_tau and each inner incidence is exactly the
-- four R571 multiplier-difference channels (++,+-,-+,--), pushed through the
-- same R145 outer slot kernel.
--
-- No self/external split, norm, absolute value, shell count, division, or
-- analytic estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230WeightRound798Exact as R798

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 2

module SeparatedFourHelicity
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

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  W = R798.separatedWeight F

  module Nested =
    R573.WeightedNested W S L H system velocityTransverse

  companionCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  companionCell =
    R438.exhaustiveWeightedCompanionCell W S system

  nestedFourHelicityCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  nestedFourHelicityCell =
    Nested.nestedWeightedCompanionCell

  fourSignInner :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  fourSignInner = Nested.Inner.fourSignInner

  companionDoubleIsNestedPointwise :
    (tau : Physical.PhysicalTriadIncidence) →
    C3.complex3Add (companionCell tau) (companionCell tau)
    ≡ nestedFourHelicityCell tau
  companionDoubleIsNestedPointwise =
    Nested.doubleExhaustiveCompanionIsNested

  foldCongruent :
    (left right :
      Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector left items ≡ R224.foldVector right items
  foldCongruent left right pointwise [] = refl
  foldCongruent left right pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (pointwise tau)
      (foldCongruent left right pointwise rest)

  companionFold :
    List Physical.PhysicalTriadIncidence → C3.Complex3 F
  companionFold = R224.foldVector companionCell

  nestedFourHelicityFold :
    List Physical.PhysicalTriadIncidence → C3.Complex3 F
  nestedFourHelicityFold = R224.foldVector nestedFourHelicityCell

  doubleCompanionFoldIsNested :
    (items : List Physical.PhysicalTriadIncidence) →
    C3.complex3Add
      (companionFold items)
      (companionFold items)
    ≡ nestedFourHelicityFold items
  doubleCompanionFoldIsNested items =
    trans
      (sym (R230.foldAdd companionCell companionCell items))
      (foldCongruent
        (λ tau → C3.complex3Add (companionCell tau) (companionCell tau))
        nestedFourHelicityCell
        companionDoubleIsNestedPointwise
        items)

  fixedOutputCompanionFold :
    Z3.FourierMode → C3.Complex3 F
  fixedOutputCompanionFold output =
    companionFold (Output.physicalOutputFiber cutoff output)

  fixedOutputNestedFourHelicityFold :
    Z3.FourierMode → C3.Complex3 F
  fixedOutputNestedFourHelicityFold output =
    nestedFourHelicityFold (Output.physicalOutputFiber cutoff output)

  fixedOutputDoubleCompanionIsNested :
    (output : Z3.FourierMode) →
    C3.complex3Add
      (fixedOutputCompanionFold output)
      (fixedOutputCompanionFold output)
    ≡ fixedOutputNestedFourHelicityFold output
  fixedOutputDoubleCompanionIsNested output =
    doubleCompanionFoldIsNested
      (Output.physicalOutputFiber cutoff output)

  fixedOutputCompanionWork :
    (mixed : Z3.FourierMode → C3.Complex3 F) →
    Z3.FourierMode → ℚ
  fixedOutputCompanionWork mixed output =
    Work.coherentWork
      (mixed output)
      (fixedOutputCompanionFold output)

  fixedOutputNestedFourHelicityWork :
    (mixed : Z3.FourierMode → C3.Complex3 F) →
    Z3.FourierMode → ℚ
  fixedOutputNestedFourHelicityWork mixed output =
    Work.coherentWork
      (mixed output)
      (fixedOutputNestedFourHelicityFold output)

  fixedOutputNestedWorkIsDoubleCompanionWork :
    (mixed : Z3.FourierMode → C3.Complex3 F) →
    (output : Z3.FourierMode) →
    fixedOutputNestedFourHelicityWork mixed output
    ≡ two * fixedOutputCompanionWork mixed output
  fixedOutputNestedWorkIsDoubleCompanionWork mixed output =
    let
      M = mixed output
      C = fixedOutputCompanionFold output
    in
    trans
      (cong
        (Work.coherentWork M)
        (sym (fixedOutputDoubleCompanionIsNested output)))
      (trans
        (Work.workAddRight M C C)
        (solve (Work.coherentWork M C ∷ two ∷ [])))

round812SeparatedMaskPreservedBeforeR573Expansion : Bool
round812SeparatedMaskPreservedBeforeR573Expansion = true

round812R438CompanionDoubleIsNestedFourHelicity : Bool
round812R438CompanionDoubleIsNestedFourHelicity = true

round812NestedWorkIsDoubleCompanionWork : Bool
round812NestedWorkIsDoubleCompanionWork = true

round812InnerCarrierIsLiteralR571FourSignMultiplierDifference : Bool
round812InnerCarrierIsLiteralR571FourSignMultiplierDifference = true

round812SelfExternalSplitRequired : Bool
round812SelfExternalSplitRequired = false

round812IntroducesEstimate : Bool
round812IntroducesEstimate = false

round812QQuotientIdentifiedWithNestedWork : Bool
round812QQuotientIdentifiedWithNestedWork = false

round812W2Closed : Bool
round812W2Closed = false

round812ClayPromotion : Bool
round812ClayPromotion = false

round812SeparatedMaskPreservedBeforeR573ExpansionIsTrue :
  round812SeparatedMaskPreservedBeforeR573Expansion ≡ true
round812SeparatedMaskPreservedBeforeR573ExpansionIsTrue = refl

round812NestedWorkIsDoubleCompanionWorkIsTrue :
  round812NestedWorkIsDoubleCompanionWork ≡ true
round812NestedWorkIsDoubleCompanionWorkIsTrue = refl

round812QQuotientIdentifiedWithNestedWorkIsFalse :
  round812QQuotientIdentifiedWithNestedWork ≡ false
round812QQuotientIdentifiedWithNestedWorkIsFalse = refl

round812IntroducesEstimateIsFalse :
  round812IntroducesEstimate ≡ false
round812IntroducesEstimateIsFalse = refl

round812W2ClosedIsFalse :
  round812W2Closed ≡ false
round812W2ClosedIsFalse = refl

round812ClayPromotionIsFalse :
  round812ClayPromotion ≡ false
round812ClayPromotionIsFalse = refl
