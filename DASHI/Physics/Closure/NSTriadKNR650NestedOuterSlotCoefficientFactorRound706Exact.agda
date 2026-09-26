{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650NestedOuterSlotCoefficientFactorRound706Exact where

------------------------------------------------------------------------
-- ROUND706 / CARRY R702'S INNER COEFFICIENT THROUGH THE ACTUAL R573 OUTER SLOT
--
-- R702 gives one inner channel
--
--   M_sigma^{s,t} = c_sigma^{s,t} X_sigma^{s,t},
--
-- with
--
--   X_sigma^{s,t} = P_p(u_a^s x u_b^t).
--
-- R700 does NOT pair X_sigma directly with the spectator.  The actual R573
-- nested cell first applies the outer slot map and multiplication by i:
--
--   i K(P_beta,Q_beta,M_sigma^{s,t},u_q).
--
-- The slot kernel is complex-linear in its first amplitude.  Therefore
--
--   i K(P,Q,c X,u_q) = c [ i K(P,Q,X,u_q) ].
--
-- Hermitian scale-right linearity then gives, for the actual spectator A,
--
--   <A, i K(P,Q,M_sigma,u_q)>
--     = c <A, i K(P,Q,X_sigma,u_q)>.
--
-- This is the correct coefficient/geometry split on the literal R700 inner
-- summand.  It supersedes any attempt to use the raw inner projected vector as
-- if it were already the outer commutator cell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityCoefficientRound702Exact as R702

slotKernelScaleFirstAmplitude :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (P Q a b : C3.Complex3 F) →
  R145.slotKernel P Q (C3.complex3Scale scalar a) b
  ≡
  C3.complex3Scale scalar (R145.slotKernel P Q a b)
slotKernelScaleFirstAmplitude scalar P Q a b =
  trans
    (cong₂ C3.complex3Subtract
      (trans
        (cong
          (λ inner → Cross.complex3Cross inner b)
          (R94.crossScaleRight scalar P a))
        (R94.crossScaleLeft scalar
          (Cross.complex3Cross P a) b))
      (R94.crossScaleLeft scalar a
        (Cross.complex3Cross Q b)))
    (sym
      (R73.complex3ScaleSubtract scalar
        (Cross.complex3Cross
          (Cross.complex3Cross P a) b)
        (Cross.complex3Cross a
          (Cross.complex3Cross Q b))))

module NestedOuterFactor
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module K =
    R702.CoefficientNormalForm system S L velocityTransverse

  velocity = Audit.velocity system

  outerP outerQ :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  outerP beta =
    R167.normalizedDirection E S (Physical.p beta)
  outerQ beta =
    R167.normalizedDirection E S (Physical.q beta)

  outerVelocityQ :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  outerVelocityQ beta = velocity (Physical.q beta)

  innerGeometry :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  innerGeometry sigma signA signB =
    K.projectedHelicalCross sigma signA signB

  outerSlotGeometry :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  outerSlotGeometry beta sigma signA signB =
    R145.slotKernel
      (outerP beta)
      (outerQ beta)
      (innerGeometry sigma signA signB)
      (outerVelocityQ beta)

  nestedGeometry :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  nestedGeometry beta sigma signA signB =
    C3.complex3Scale (C3.complexI F)
      (outerSlotGeometry beta sigma signA signB)

  actualNestedChannel :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex3 F
  actualNestedChannel beta sigma signA signB =
    C3.complex3Scale (C3.complexI F)
      (R145.slotKernel
        (outerP beta)
        (outerQ beta)
        (K.C.multiplierDifferenceVector sigma signA signB)
        (outerVelocityQ beta))

  outerSlotChannelFactorsCoefficient :
    (beta sigma : Physical.PhysicalTriadIncidence) →
    (signA signB : Helical.HelicitySign) →
    actualNestedChannel beta sigma signA signB
    ≡
    C3.complex3Scale
      (K.channelCoefficient sigma signA signB)
      (nestedGeometry beta sigma signA signB)
  outerSlotChannelFactorsCoefficient beta sigma signA signB =
    let
      coefficient = K.channelCoefficient sigma signA signB
      geometry = innerGeometry sigma signA signB
      P = outerP beta
      Q = outerQ beta
      uq = outerVelocityQ beta
      slot = R145.slotKernel P Q geometry uq
    in
    trans
      (cong
        (C3.complex3Scale (C3.complexI F))
        (trans
          (cong
            (λ value → R145.slotKernel P Q value uq)
            (K.multiplierDifferenceIsCoefficientTimesProjectedCross
              sigma signA signB))
          (slotKernelScaleFirstAmplitude coefficient P Q geometry uq)))
      (trans
        (R73.complex3ScaleAssociative
          (C3.complexI F) coefficient slot)
        (trans
          (cong
            (λ scalar → C3.complex3Scale scalar slot)
            (Algebra.complexMultiplyCommutative
              (C3.complexI F) coefficient))
          (sym
            (R73.complex3ScaleAssociative
              coefficient (C3.complexI F) slot))))

  actualNestedChannelPairingFactorsCoefficient :
    (spectator : C3.Complex3 F) →
    (beta sigma : Physical.PhysicalTriadIncidence) →
    (signA signB : Helical.HelicitySign) →
    C3.hermitianPairing3 spectator
      (actualNestedChannel beta sigma signA signB)
    ≡
    C3.complexMultiply
      (K.channelCoefficient sigma signA signB)
      (C3.hermitianPairing3 spectator
        (nestedGeometry beta sigma signA signB))
  actualNestedChannelPairingFactorsCoefficient
      spectator beta sigma signA signB =
    trans
      (cong
        (C3.hermitianPairing3 spectator)
        (outerSlotChannelFactorsCoefficient beta sigma signA signB))
      (Scaling.hermitianPairingScaleRight
        (K.channelCoefficient sigma signA signB)
        spectator
        (nestedGeometry beta sigma signA signB))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round706SlotKernelComplexLinearInForcingAmplitude : Bool
round706SlotKernelComplexLinearInForcingAmplitude = true

round706R702CoefficientCarriedThroughActualR573OuterSlot : Bool
round706R702CoefficientCarriedThroughActualR573OuterSlot = true

round706ActualNestedSpectatorPairingFactorsCoefficient : Bool
round706ActualNestedSpectatorPairingFactorsCoefficient = true

round706R703RawInnerPairingAlreadyEqualsR700NestedPairing : Bool
round706R703RawInnerPairingAlreadyEqualsR700NestedPairing = false

round706IntroducesEstimate : Bool
round706IntroducesEstimate = false

round706ClayPromotion : Bool
round706ClayPromotion = false

round706SlotKernelComplexLinearInForcingAmplitudeIsTrue :
  round706SlotKernelComplexLinearInForcingAmplitude ≡ true
round706SlotKernelComplexLinearInForcingAmplitudeIsTrue = refl

round706R702CoefficientCarriedThroughActualR573OuterSlotIsTrue :
  round706R702CoefficientCarriedThroughActualR573OuterSlot ≡ true
round706R702CoefficientCarriedThroughActualR573OuterSlotIsTrue = refl

round706ActualNestedSpectatorPairingFactorsCoefficientIsTrue :
  round706ActualNestedSpectatorPairingFactorsCoefficient ≡ true
round706ActualNestedSpectatorPairingFactorsCoefficientIsTrue = refl

round706R703RawInnerPairingAlreadyEqualsR700NestedPairingIsFalse :
  round706R703RawInnerPairingAlreadyEqualsR700NestedPairing ≡ false
round706R703RawInnerPairingAlreadyEqualsR700NestedPairingIsFalse = refl

round706IntroducesEstimateIsFalse :
  round706IntroducesEstimate ≡ false
round706IntroducesEstimateIsFalse = refl

round706ClayPromotionIsFalse :
  round706ClayPromotion ≡ false
round706ClayPromotionIsFalse = refl
