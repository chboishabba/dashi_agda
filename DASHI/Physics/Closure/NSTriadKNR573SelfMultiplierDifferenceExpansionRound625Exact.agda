{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR573SelfMultiplierDifferenceExpansionRound625Exact where

------------------------------------------------------------------------
-- ROUND625 / R573 SELF SLOT -> FOUR SELECTED HELICAL MULTIPLIER DIFFERENCES
--
-- R624 leaves two honest signed analytic channels.  This owner sharpens the
-- self channel without estimating it.
--
-- On R573's nonzero outer branch the forcing slot is p.  The selected
-- self-forcing there is exactly the stored ordered-pair interaction of the
-- p-energy leg.  R571 decomposes that same ordered pair into the four helical
-- sign channels
--
--   (++), (+-), (-+), (--),
--
-- each carrying an exact signed modal multiplier difference.  Since R145's
-- slot kernel is additive in its forcing amplitude, the R613 weighted self slot
-- is exactly the corresponding sum of four multiplier-difference slot cells.
--
-- The p=0 branch remains the literal zero branch already used by R573.
-- No norm, absolute value, estimate, or cancellation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact as R309
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613

module SelfMultiplierExpansion
    {r} {F : C3.RealField r}
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

  module Split =
    R613.NestedNetworkSplit W S L H system velocityTransverse
  module Components =
    R571.Componentwise system S L velocityTransverse

  velocity = Audit.velocity system

  pNonzeroFromDecision :
    (tau : Physical.PhysicalTriadIncidence) →
    Output.modeEqual (Physical.p tau) Z3.zeroMode ≡ false →
    Z3.NonZeroMode (Physical.p tau)
  pNonzeroFromDecision tau pDecision = record
    { Z3.notZero = λ pZero →
        Output.falseNotTrue
          (trans
            (sym pDecision)
            (Output.modeEqualComplete pZero))
    }

  pEnergyLegOutputNonzero :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p tau) →
    Z3.NonZeroMode (Physical.k (Orbit.pEnergyLeg tau))
  pEnergyLegOutputNonzero tau pNonzero =
    subst
      Z3.NonZeroMode
      (sym (Orbit.pEnergyLegOutput tau))
      pNonzero

  selfMultiplierVector :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign → Helical.HelicitySign →
    C3.Complex3 F
  selfMultiplierVector tau signA signB =
    Components.multiplierDifferenceVector
      (Orbit.pEnergyLeg tau) signA signB

  fourSelfMultiplierVectors :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  fourSelfMultiplierVectors tau =
    C3.complex3Add
      (C3.complex3Add
        (selfMultiplierVector tau Helical.plus Helical.plus)
        (selfMultiplierVector tau Helical.plus Helical.minus))
      (C3.complex3Add
        (selfMultiplierVector tau Helical.minus Helical.plus)
        (selfMultiplierVector tau Helical.minus Helical.minus))

  selfForcingPIsFourMultiplierDifferences :
    (tau : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
    R95.selfForcingP system tau
    ≡ fourSelfMultiplierVectors tau
  selfForcingPIsFourMultiplierDifferences tau pNonzero =
    trans
      refl
      (Components.partnerVectorSumIsFourMultiplierDifferences
        (Orbit.pEnergyLeg tau)
        (pEnergyLegOutputNonzero tau pNonzero))

  multiplierSlot :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign → Helical.HelicitySign →
    C3.Complex3 F
  multiplierSlot tau signA signB =
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p tau))
      (R167.normalizedDirection E S (Physical.q tau))
      (selfMultiplierVector tau signA signB)
      (velocity (Physical.q tau))

  fourMultiplierSlots :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  fourMultiplierSlots tau =
    C3.complex3Add
      (C3.complex3Add
        (multiplierSlot tau Helical.plus Helical.plus)
        (multiplierSlot tau Helical.plus Helical.minus))
      (C3.complex3Add
        (multiplierSlot tau Helical.minus Helical.plus)
        (multiplierSlot tau Helical.minus Helical.minus))

  slotOfFourMultiplierVectorsIsFourSlots :
    (tau : Physical.PhysicalTriadIncidence) →
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p tau))
      (R167.normalizedDirection E S (Physical.q tau))
      (fourSelfMultiplierVectors tau)
      (velocity (Physical.q tau))
    ≡ fourMultiplierSlots tau
  slotOfFourMultiplierVectorsIsFourSlots tau =
    let
      P = R167.normalizedDirection E S (Physical.p tau)
      Q = R167.normalizedDirection E S (Physical.q tau)
      b = velocity (Physical.q tau)
      pp = selfMultiplierVector tau Helical.plus Helical.plus
      pm = selfMultiplierVector tau Helical.plus Helical.minus
      mp = selfMultiplierVector tau Helical.minus Helical.plus
      mm = selfMultiplierVector tau Helical.minus Helical.minus
    in
    trans
      (R309.slotKernelAdditiveFirstAmplitude
        P Q
        (C3.complex3Add pp pm)
        (C3.complex3Add mp mm)
        b)
      (cong₂ C3.complex3Add
        (R309.slotKernelAdditiveFirstAmplitude P Q pp pm b)
        (R309.slotKernelAdditiveFirstAmplitude P Q mp mm b))

  weightedFourMultiplierSlots :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedFourMultiplierSlots tau =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F)
        (fourMultiplierSlots tau))

  weightedSelfSlotIsFourMultiplierSlots :
    (tau : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
    Split.weightedSelfSlot tau
    ≡ weightedFourMultiplierSlots tau
  weightedSelfSlotIsFourMultiplierSlots tau pNonzero =
    trans
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (cong
          (C3.complex3Scale (C3.complexI F))
          (cong
            (λ forcing →
              R145.slotKernel
                (R167.normalizedDirection E S (Physical.p tau))
                (R167.normalizedDirection E S (Physical.q tau))
                forcing
                (velocity (Physical.q tau)))
            (selfForcingPIsFourMultiplierDifferences tau pNonzero))))
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (cong
          (C3.complex3Scale (C3.complexI F))
          (slotOfFourMultiplierVectorsIsFourSlots tau)))

  selfExhaustiveCompanionMultiplierNormalForm :
    (tau : Physical.PhysicalTriadIncidence) →
    Split.selfExhaustiveCompanion tau
    ≡
    let pDecision =
          Output.modeEqual (Physical.p tau) Z3.zeroMode
    in
    if pDecision then C3.complex3Zero F
    else weightedFourMultiplierSlots tau
  selfExhaustiveCompanionMultiplierNormalForm tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
  ... | true = refl
  ... | false =
    weightedSelfSlotIsFourMultiplierSlots
      tau (pNonzeroFromDecision tau pDecision)

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round625SelfForcingPFourHelicityMultiplierDifferencesClosed : Bool
round625SelfForcingPFourHelicityMultiplierDifferencesClosed = true

round625R573SelfSlotFourMultiplierDifferenceNormalFormClosed : Bool
round625R573SelfSlotFourMultiplierDifferenceNormalFormClosed = true

round625ZeroPBranchPreserved : Bool
round625ZeroPBranchPreserved = true

round625IntroducesNormOrAbsoluteValue : Bool
round625IntroducesNormOrAbsoluteValue = false

round625IntroducesEstimate : Bool
round625IntroducesEstimate = false

round625SelfSignedPaymentClosed : Bool
round625SelfSignedPaymentClosed = false

round625SelfForcingPFourHelicityMultiplierDifferencesClosedIsTrue :
  round625SelfForcingPFourHelicityMultiplierDifferencesClosed ≡ true
round625SelfForcingPFourHelicityMultiplierDifferencesClosedIsTrue = refl

round625R573SelfSlotFourMultiplierDifferenceNormalFormClosedIsTrue :
  round625R573SelfSlotFourMultiplierDifferenceNormalFormClosed ≡ true
round625R573SelfSlotFourMultiplierDifferenceNormalFormClosedIsTrue = refl

round625IntroducesNormOrAbsoluteValueIsFalse :
  round625IntroducesNormOrAbsoluteValue ≡ false
round625IntroducesNormOrAbsoluteValueIsFalse = refl

round625IntroducesEstimateIsFalse :
  round625IntroducesEstimate ≡ false
round625IntroducesEstimateIsFalse = refl

round625SelfSignedPaymentClosedIsFalse :
  round625SelfSignedPaymentClosed ≡ false
round625SelfSignedPaymentClosedIsFalse = refl
