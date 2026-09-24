{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNSelfHomochiralHeterochiralSplitRound632Exact where

------------------------------------------------------------------------
-- ROUND632 / SELF R573 = HOMOCHIRAL RADIAL + HETEROCHIRAL LITERAL
--
-- R625 writes the selected-self R573 forcing slot as the four exact R571
-- multiplier-difference channels
--
--   (++), (+-), (-+), (--).
--
-- The existing R571 homochiral specialization proves on the SAME physical
-- carrier that ++ and -- are exact signed radial-increment vectors.  This owner
-- only regroups the fixed four channels as
--
--   (++ + +-) + (-+ + --)
--     = (++ + --) + (+- + -+),
--
-- transports the ++/-- terms through the existing radial same-object weld,
-- and carries that split through:
--
--   * the literal slot kernel;
--   * the spectator/R294 weight;
--   * the actual p=0 exhaustive branch;
--   * the doubled R573 nested companion.
--
-- The heterochiral (+-,-+) channels remain literal radial-sum channels.
-- No norm, absolute value, estimate, heterochiral promotion, or spacetime
-- bound is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeFullSwapAntisymmetryRound119Exact as R119
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNMixedHelicityDampedProductTangentRound231Exact as R231
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact as R309
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR573SelfMultiplierDifferenceExpansionRound625Exact as R625
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Homo

F : C3.RealField _
F = Rational.rationalRealField

module SelfHelicitySplit632
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Base =
    R625.SelfMultiplierExpansion W S L H system velocityTransverse

  module Radial =
    Homo.PhysicalHomochiral E I system S L velocityTransverse

  velocity = Audit.velocity system

  homochiralVector :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  homochiralVector tau =
    C3.complex3Add
      (Radial.homochiralRadialVector R311.plus Helical.plus tau)
      (Radial.homochiralRadialVector R311.minus Helical.minus tau)

  heterochiralVector :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  heterochiralVector tau =
    C3.complex3Add
      (Base.selfMultiplierVector tau Helical.plus Helical.minus)
      (Base.selfMultiplierVector tau Helical.minus Helical.plus)

  fourSelfMultiplierVectorsSplit :
    (tau : Physical.PhysicalTriadIncidence) →
    Base.fourSelfMultiplierVectors tau
    ≡ C3.complex3Add
        (homochiralVector tau)
        (heterochiralVector tau)
  fourSelfMultiplierVectorsSplit tau =
    let
      pp = Base.selfMultiplierVector tau Helical.plus Helical.plus
      pm = Base.selfMultiplierVector tau Helical.plus Helical.minus
      mp = Base.selfMultiplierVector tau Helical.minus Helical.plus
      mm = Base.selfMultiplierVector tau Helical.minus Helical.minus

      reorderSecond :
        C3.complex3Add
          (C3.complex3Add pp pm)
          (C3.complex3Add mp mm)
        ≡
        C3.complex3Add
          (C3.complex3Add pp pm)
          (C3.complex3Add mm mp)
      reorderSecond =
        cong
          (C3.complex3Add (C3.complex3Add pp pm))
          (R119.complex3AddCommutative mp mm)

      regroup :
        C3.complex3Add
          (C3.complex3Add pp pm)
          (C3.complex3Add mm mp)
        ≡
        C3.complex3Add
          (C3.complex3Add pp mm)
          (C3.complex3Add pm mp)
      regroup = R231.complex3RegroupFour pp pm mm mp

      radial :
        C3.complex3Add pp mm
        ≡ homochiralVector tau
      radial =
        cong₂ C3.complex3Add
          (Radial.plusMultiplierDifferenceVectorIsRadial tau)
          (Radial.minusMultiplierDifferenceVectorIsRadial tau)
    in
    trans reorderSecond
      (trans regroup
        (cong₂ C3.complex3Add radial refl))

  homochiralSlot :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  homochiralSlot tau =
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p tau))
      (R167.normalizedDirection E S (Physical.q tau))
      (homochiralVector tau)
      (velocity (Physical.q tau))

  heterochiralSlot :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  heterochiralSlot tau =
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p tau))
      (R167.normalizedDirection E S (Physical.q tau))
      (heterochiralVector tau)
      (velocity (Physical.q tau))

  fourMultiplierSlotsSplit :
    (tau : Physical.PhysicalTriadIncidence) →
    Base.fourMultiplierSlots tau
    ≡ C3.complex3Add
        (homochiralSlot tau)
        (heterochiralSlot tau)
  fourMultiplierSlotsSplit tau =
    let
      P = R167.normalizedDirection E S (Physical.p tau)
      Q = R167.normalizedDirection E S (Physical.q tau)
      b = velocity (Physical.q tau)
    in
    trans
      (sym (Base.slotOfFourMultiplierVectorsIsFourSlots tau))
      (trans
        (cong
          (λ forcing → R145.slotKernel P Q forcing b)
          (fourSelfMultiplierVectorsSplit tau))
        (R309.slotKernelAdditiveFirstAmplitude
          P Q
          (homochiralVector tau)
          (heterochiralVector tau)
          b))

  weightedHomochiralSlot weightedHeterochiralSlot :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedHomochiralSlot tau =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F)
        (homochiralSlot tau))
  weightedHeterochiralSlot tau =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F)
        (heterochiralSlot tau))

  weightedFourMultiplierSlotsSplit :
    (tau : Physical.PhysicalTriadIncidence) →
    Base.weightedFourMultiplierSlots tau
    ≡ C3.complex3Add
        (weightedHomochiralSlot tau)
        (weightedHeterochiralSlot tau)
  weightedFourMultiplierSlotsSplit tau =
    trans
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (cong
          (C3.complex3Scale (C3.complexI F))
          (fourMultiplierSlotsSplit tau)))
      (trans
        (cong
          (C3.complex3Scale (R294.weight W tau))
          (R73.complex3ScaleAdd
            (C3.complexI F)
            (homochiralSlot tau)
            (heterochiralSlot tau)))
        (R73.complex3ScaleAdd
          (R294.weight W tau)
          (C3.complex3Scale (C3.complexI F) (homochiralSlot tau))
          (C3.complex3Scale (C3.complexI F) (heterochiralSlot tau))))

  homochiralExhaustive heterochiralExhaustive :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  homochiralExhaustive tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false = weightedHomochiralSlot tau
  heterochiralExhaustive tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false = weightedHeterochiralSlot tau

  selfMultiplierExhaustiveSplits :
    (tau : Physical.PhysicalTriadIncidence) →
    Base.selfMultiplierExhaustiveCompanion tau
    ≡ C3.complex3Add
        (homochiralExhaustive tau)
        (heterochiralExhaustive tau)
  selfMultiplierExhaustiveSplits tau
      with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true =
    sym (Algebra.complex3AddZeroRight (C3.complex3Zero F))
  ... | false =
    weightedFourMultiplierSlotsSplit tau

  homochiralNested heterochiralNested :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  homochiralNested tau =
    C3.complex3Add
      (homochiralExhaustive tau)
      (homochiralExhaustive tau)
  heterochiralNested tau =
    C3.complex3Add
      (heterochiralExhaustive tau)
      (heterochiralExhaustive tau)

  selfNestedMultiplierSplits :
    (tau : Physical.PhysicalTriadIncidence) →
    Base.selfNestedMultiplierCompanion tau
    ≡ C3.complex3Add
        (homochiralNested tau)
        (heterochiralNested tau)
  selfNestedMultiplierSplits tau =
    let
      h = homochiralExhaustive tau
      e = heterochiralExhaustive tau
    in
    trans
      (cong₂ C3.complex3Add
        (selfMultiplierExhaustiveSplits tau)
        (selfMultiplierExhaustiveSplits tau))
      (trans
        (R231.complex3RegroupFour h e h e)
        refl)

  selfR573NestedSplitsHomochiralHeterochiral :
    (tau : Physical.PhysicalTriadIncidence) →
    Base.Split.selfNestedWeightedCompanionCell tau
    ≡ C3.complex3Add
        (homochiralNested tau)
        (heterochiralNested tau)
  selfR573NestedSplitsHomochiralHeterochiral tau =
    trans
      (Base.selfNestedCompanionMultiplierNormalForm tau)
      (selfNestedMultiplierSplits tau)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round632SelfFourHelicitySplitClosed : Bool
round632SelfFourHelicitySplitClosed = true

round632HomochiralR571RadialCarrierWeldReused : Bool
round632HomochiralR571RadialCarrierWeldReused =
  Homo.r571HomochiralRadialCarrierWeldClosed

round632SelfR573NestedHomochiralHeterochiralSplitClosed : Bool
round632SelfR573NestedHomochiralHeterochiralSplitClosed = true

round632ZeroPBranchPreserved : Bool
round632ZeroPBranchPreserved = true

round632HeterochiralChannelsRemainLiteral : Bool
round632HeterochiralChannelsRemainLiteral = true

round632HeterochiralPromotionIntroduced : Bool
round632HeterochiralPromotionIntroduced = false

round632IntroducesEstimate : Bool
round632IntroducesEstimate = false

round632SelfSignedPaymentClosed : Bool
round632SelfSignedPaymentClosed = false

round632SelfFourHelicitySplitClosedIsTrue :
  round632SelfFourHelicitySplitClosed ≡ true
round632SelfFourHelicitySplitClosedIsTrue = refl

round632SelfR573NestedHomochiralHeterochiralSplitClosedIsTrue :
  round632SelfR573NestedHomochiralHeterochiralSplitClosed ≡ true
round632SelfR573NestedHomochiralHeterochiralSplitClosedIsTrue = refl

round632ZeroPBranchPreservedIsTrue :
  round632ZeroPBranchPreserved ≡ true
round632ZeroPBranchPreservedIsTrue = refl

round632HeterochiralChannelsRemainLiteralIsTrue :
  round632HeterochiralChannelsRemainLiteral ≡ true
round632HeterochiralChannelsRemainLiteralIsTrue = refl

round632HeterochiralPromotionIntroducedIsFalse :
  round632HeterochiralPromotionIntroduced ≡ false
round632HeterochiralPromotionIntroducedIsFalse = refl

round632IntroducesEstimateIsFalse :
  round632IntroducesEstimate ≡ false
round632IntroducesEstimateIsFalse = refl

round632SelfSignedPaymentClosedIsFalse :
  round632SelfSignedPaymentClosed ≡ false
round632SelfSignedPaymentClosedIsFalse = refl
