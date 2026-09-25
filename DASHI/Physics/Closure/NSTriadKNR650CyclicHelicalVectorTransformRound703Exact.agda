{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CyclicHelicalVectorTransformRound703Exact where

------------------------------------------------------------------------
-- ROUND703 / FULL THREE-OUTER-LEG TRANSFORMATION OF ONE HELICAL CHANNEL
--
-- R702 exposes one inner channel as
--
--   (lambda_t(b)-lambda_s(a)) P_p(u_a^s x u_b^t).
--
-- The remaining Clay-facing question is not scalar coefficient arithmetic:
-- R700 cyclically evaluates the corresponding vector on the three OUTER
-- presentations beta, pEnergyLeg beta, qEnergyLeg beta.
--
-- This file computes those three vectors exactly.  Assuming only the physical
-- Fourier reality law and the standard evenness |-|=| | of the mode norm,
--
-- base:
--   [lambda_t(q)-lambda_s(p)] P_k(u_p^s x u_q^t)
--
-- p-energy leg:
--   [lambda_t(q)-lambda_s(k)] P_p(u_k^s x conjugate(u_q^t))
--
-- q-energy leg:
--   [lambda_t(p)-lambda_s(k)] P_q(u_k^s x conjugate(u_p^t)).
--
-- The helicity sign does NOT flip under Fourier conjugation: that is exactly
-- the existing helicalProjectorRealityCompatible law.
--
-- No cancellation is claimed.  R703 isolates the literal three-vector sum
-- whose exact vanishing or cutoff-uniform signed spacetime estimate is now
-- the highest-alpha nonlinear task.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityCoefficientRound702Exact as R702

module CyclicChannel
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (velocityReality : Reality.RealityCondition (Audit.velocity system))
    (modeNormEven :
      (mode : Z3.FourierMode) →
      Helical.modeNorm S (Z3.negateMode mode)
      ≡ Helical.modeNorm S mode) where

  module K =
    R702.CoefficientNormalForm system S L velocityTransverse

  componentReality :
    (sign : Helical.HelicitySign) →
    (mode : Z3.FourierMode) →
    K.C.component sign (Z3.negateMode mode)
    ≡ C3.complex3Conjugate (K.C.component sign mode)
  componentReality sign mode =
    trans
      (cong
        (Helical.helicalProjector E I S sign (Z3.negateMode mode))
        (velocityReality mode))
      (Helical.helicalProjectorRealityCompatible
        L sign mode (Audit.velocity system mode))

  signedEigenvalueEven :
    (sign : Helical.HelicitySign) →
    (mode : Z3.FourierMode) →
    K.C.signedEigenvalue sign (Z3.negateMode mode)
    ≡ K.C.signedEigenvalue sign mode
  signedEigenvalueEven Helical.plus mode =
    cong (C3.realEmbed F) (modeNormEven mode)
  signedEigenvalueEven Helical.minus mode =
    cong
      (C3.realEmbed F)
      (cong (C3.negate F) (modeNormEven mode))

  baseChannelVector :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  baseChannelVector beta signP signQ =
    C3.complex3Scale
      (C3.complexSubtract
        (K.C.signedEigenvalue signQ (Physical.q beta))
        (K.C.signedEigenvalue signP (Physical.p beta)))
      (C3.lerayProject3 E I (Physical.k beta)
        (Cross.complex3Cross
          (K.C.component signP (Physical.p beta))
          (K.C.component signQ (Physical.q beta))))

  pLegChannelVector :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  pLegChannelVector beta signK signQ =
    C3.complex3Scale
      (C3.complexSubtract
        (K.C.signedEigenvalue signQ (Physical.q beta))
        (K.C.signedEigenvalue signK (Physical.k beta)))
      (C3.lerayProject3 E I (Physical.p beta)
        (Cross.complex3Cross
          (K.C.component signK (Physical.k beta))
          (C3.complex3Conjugate
            (K.C.component signQ (Physical.q beta)))))

  qLegChannelVector :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  qLegChannelVector beta signK signP =
    C3.complex3Scale
      (C3.complexSubtract
        (K.C.signedEigenvalue signP (Physical.p beta))
        (K.C.signedEigenvalue signK (Physical.k beta)))
      (C3.lerayProject3 E I (Physical.q beta)
        (Cross.complex3Cross
          (K.C.component signK (Physical.k beta))
          (C3.complex3Conjugate
            (K.C.component signP (Physical.p beta)))))

  baseChannelMeaning :
    (beta : Physical.PhysicalTriadIncidence) →
    (signP signQ : Helical.HelicitySign) →
    K.C.multiplierDifferenceVector beta signP signQ
    ≡ baseChannelVector beta signP signQ
  baseChannelMeaning beta signP signQ = refl

  pEnergyLegCoefficient :
    (beta : Physical.PhysicalTriadIncidence) →
    (signK signQ : Helical.HelicitySign) →
    K.channelCoefficient (Orbit.pEnergyLeg beta) signK signQ
    ≡
    C3.complexSubtract
      (K.C.signedEigenvalue signQ (Physical.q beta))
      (K.C.signedEigenvalue signK (Physical.k beta))
  pEnergyLegCoefficient beta signK signQ =
    cong
      (λ eigen →
        C3.complexSubtract
          eigen
          (K.C.signedEigenvalue signK (Physical.k beta)))
      (signedEigenvalueEven signQ (Physical.q beta))

  qEnergyLegCoefficient :
    (beta : Physical.PhysicalTriadIncidence) →
    (signK signP : Helical.HelicitySign) →
    K.channelCoefficient (Orbit.qEnergyLeg beta) signK signP
    ≡
    C3.complexSubtract
      (K.C.signedEigenvalue signP (Physical.p beta))
      (K.C.signedEigenvalue signK (Physical.k beta))
  qEnergyLegCoefficient beta signK signP =
    cong
      (λ eigen →
        C3.complexSubtract
          eigen
          (K.C.signedEigenvalue signK (Physical.k beta)))
      (signedEigenvalueEven signP (Physical.p beta))

  pEnergyLegProjectedCross :
    (beta : Physical.PhysicalTriadIncidence) →
    (signK signQ : Helical.HelicitySign) →
    K.projectedHelicalCross
      (Orbit.pEnergyLeg beta) signK signQ
    ≡
    C3.lerayProject3 E I (Physical.p beta)
      (Cross.complex3Cross
        (K.C.component signK (Physical.k beta))
        (C3.complex3Conjugate
          (K.C.component signQ (Physical.q beta))))
  pEnergyLegProjectedCross beta signK signQ =
    cong
      (C3.lerayProject3 E I (Physical.p beta))
      (cong
        (Cross.complex3Cross
          (K.C.component signK (Physical.k beta)))
        (componentReality signQ (Physical.q beta)))

  qEnergyLegProjectedCross :
    (beta : Physical.PhysicalTriadIncidence) →
    (signK signP : Helical.HelicitySign) →
    K.projectedHelicalCross
      (Orbit.qEnergyLeg beta) signK signP
    ≡
    C3.lerayProject3 E I (Physical.q beta)
      (Cross.complex3Cross
        (K.C.component signK (Physical.k beta))
        (C3.complex3Conjugate
          (K.C.component signP (Physical.p beta))))
  qEnergyLegProjectedCross beta signK signP =
    cong
      (C3.lerayProject3 E I (Physical.q beta))
      (cong
        (Cross.complex3Cross
          (K.C.component signK (Physical.k beta)))
        (componentReality signP (Physical.p beta)))

  pEnergyLegChannelMeaning :
    (beta : Physical.PhysicalTriadIncidence) →
    (signK signQ : Helical.HelicitySign) →
    K.C.multiplierDifferenceVector
      (Orbit.pEnergyLeg beta) signK signQ
    ≡ pLegChannelVector beta signK signQ
  pEnergyLegChannelMeaning beta signK signQ =
    trans
      (K.multiplierDifferenceIsCoefficientTimesProjectedCross
        (Orbit.pEnergyLeg beta) signK signQ)
      (trans
        (cong
          (λ coefficient →
            C3.complex3Scale coefficient
              (K.projectedHelicalCross
                (Orbit.pEnergyLeg beta) signK signQ))
          (pEnergyLegCoefficient beta signK signQ))
        (cong
          (C3.complex3Scale
            (C3.complexSubtract
              (K.C.signedEigenvalue signQ (Physical.q beta))
              (K.C.signedEigenvalue signK (Physical.k beta))))
          (pEnergyLegProjectedCross beta signK signQ)))

  qEnergyLegChannelMeaning :
    (beta : Physical.PhysicalTriadIncidence) →
    (signK signP : Helical.HelicitySign) →
    K.C.multiplierDifferenceVector
      (Orbit.qEnergyLeg beta) signK signP
    ≡ qLegChannelVector beta signK signP
  qEnergyLegChannelMeaning beta signK signP =
    trans
      (K.multiplierDifferenceIsCoefficientTimesProjectedCross
        (Orbit.qEnergyLeg beta) signK signP)
      (trans
        (cong
          (λ coefficient →
            C3.complex3Scale coefficient
              (K.projectedHelicalCross
                (Orbit.qEnergyLeg beta) signK signP))
          (qEnergyLegCoefficient beta signK signP))
        (cong
          (C3.complex3Scale
            (C3.complexSubtract
              (K.C.signedEigenvalue signP (Physical.p beta))
              (K.C.signedEigenvalue signK (Physical.k beta))))
          (qEnergyLegProjectedCross beta signK signP)))

  threeOuterLegChannel :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  threeOuterLegChannel beta signP signQ signK =
    C3.complex3Add
      (C3.complex3Add
        (baseChannelVector beta signP signQ)
        (pLegChannelVector beta signK signQ))
      (qLegChannelVector beta signK signP)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round703FourierRealityTransportedThroughHelicalProjectors : Bool
round703FourierRealityTransportedThroughHelicalProjectors = true

round703HelicitySignFlipsUnderFourierConjugation : Bool
round703HelicitySignFlipsUnderFourierConjugation = false

round703ModeNormEvennessRequiredForCyclicCoefficientNormalForm : Bool
round703ModeNormEvennessRequiredForCyclicCoefficientNormalForm = true

round703PEnergyLegVectorTransformClosed : Bool
round703PEnergyLegVectorTransformClosed = true

round703QEnergyLegVectorTransformClosed : Bool
round703QEnergyLegVectorTransformClosed = true

round703FullThreeOuterLegChannelExposed : Bool
round703FullThreeOuterLegChannelExposed = true

round703ThreeOuterLegChannelCancellationClosed : Bool
round703ThreeOuterLegChannelCancellationClosed = false

round703IntroducesEstimate : Bool
round703IntroducesEstimate = false

round703ClayPromotion : Bool
round703ClayPromotion = false

round703FourierRealityTransportedThroughHelicalProjectorsIsTrue :
  round703FourierRealityTransportedThroughHelicalProjectors ≡ true
round703FourierRealityTransportedThroughHelicalProjectorsIsTrue = refl

round703HelicitySignFlipsUnderFourierConjugationIsFalse :
  round703HelicitySignFlipsUnderFourierConjugation ≡ false
round703HelicitySignFlipsUnderFourierConjugationIsFalse = refl

round703ModeNormEvennessRequiredForCyclicCoefficientNormalFormIsTrue :
  round703ModeNormEvennessRequiredForCyclicCoefficientNormalForm ≡ true
round703ModeNormEvennessRequiredForCyclicCoefficientNormalFormIsTrue = refl

round703PEnergyLegVectorTransformClosedIsTrue :
  round703PEnergyLegVectorTransformClosed ≡ true
round703PEnergyLegVectorTransformClosedIsTrue = refl

round703QEnergyLegVectorTransformClosedIsTrue :
  round703QEnergyLegVectorTransformClosed ≡ true
round703QEnergyLegVectorTransformClosedIsTrue = refl

round703FullThreeOuterLegChannelExposedIsTrue :
  round703FullThreeOuterLegChannelExposed ≡ true
round703FullThreeOuterLegChannelExposedIsTrue = refl

round703ThreeOuterLegChannelCancellationClosedIsFalse :
  round703ThreeOuterLegChannelCancellationClosed ≡ false
round703ThreeOuterLegChannelCancellationClosedIsFalse = refl

round703IntroducesEstimateIsFalse :
  round703IntroducesEstimate ≡ false
round703IntroducesEstimateIsFalse = refl

round703ClayPromotionIsFalse :
  round703ClayPromotion ≡ false
round703ClayPromotionIsFalse = refl
