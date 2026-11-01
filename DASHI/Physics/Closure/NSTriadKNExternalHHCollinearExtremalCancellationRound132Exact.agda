module DASHI.Physics.Closure.NSTriadKNExternalHHCollinearExtremalCancellationRound132Exact where

------------------------------------------------------------------------
-- ROUND132 / PHYSICAL COLLINEAR EXTREMAL HH CELLS PAY EXACTLY ZERO
--
-- Companion Lean source:
--   RequestProject/NavierStokes/WaleffeHighHighOutputGain.lean
--
-- Round131 proves the algebraic endpoint
--
--   k.u = 0 , k.v = 0  ==>  P_k (u x v) = 0.
--
-- Here that theorem is welded to the literal Galerkin/Waleffe carrier.  We
-- keep collinearity proof-bearing: the output wave is supplied as an exact
-- scalar multiple of each input wave.  This avoids inventing a division or
-- scalar-cancellation principle on the deliberately weak generic RealField.
--
-- Own-mode incompressibility transports to output-mode transversality, so the
-- projected cross product vanishes.  Round120 then makes both the actual
-- shared-fibre partner vector sum and its tested quartic-cell sum vanish.
-- No absolute values or estimates occur.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNOutputTransverseCrossLerayCancellationRound131Exact as R131
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNPressureDirectionHermitianOrthogonalityRound84Exact as Zero

scaledWaveTransversality :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (inputWave outputWave value : C3.Complex3 F) →
  outputWave ≡ C3.complex3Scale scalar inputWave →
  C3.bilinearDot3 inputWave value ≡ C3.complexZero F →
  C3.bilinearDot3 outputWave value ≡ C3.complexZero F
scaledWaveTransversality {F = F}
    scalar inputWave outputWave value outputMeaning inputTransverse =
  trans
    (cong (λ wave → C3.bilinearDot3 wave value) outputMeaning)
    (trans
      (Scaling.bilinearDot3ScaleLeft scalar inputWave value)
      (trans
        (cong (C3.complexMultiply scalar) inputTransverse)
        (Field.complexMultiplyZeroRight scalar)))

record PhysicalCollinearExtremalData
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  constructor physical-collinear-extremal-data
  field
    outputNonzero : Z3.NonZeroMode (Physical.k tau)

    pIncompressible :
      C3.bilinearDot3
        (C3.modeVector E (Physical.p tau))
        (Audit.velocity system (Physical.p tau))
      ≡ C3.complexZero F

    qIncompressible :
      C3.bilinearDot3
        (C3.modeVector E (Physical.q tau))
        (Audit.velocity system (Physical.q tau))
      ≡ C3.complexZero F

    outputScaleFromP outputScaleFromQ : C3.Complex F

    outputWaveFromP :
      C3.modeVector E (Physical.k tau)
      ≡ C3.complex3Scale outputScaleFromP
          (C3.modeVector E (Physical.p tau))

    outputWaveFromQ :
      C3.modeVector E (Physical.k tau)
      ≡ C3.complex3Scale outputScaleFromQ
          (C3.modeVector E (Physical.q tau))

open PhysicalCollinearExtremalData public

pVelocityTransverseToOutput :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  (C : PhysicalCollinearExtremalData system tau) →
  C3.bilinearDot3
    (C3.modeVector E (Physical.k tau))
    (Audit.velocity system (Physical.p tau))
  ≡ C3.complexZero F
pVelocityTransverseToOutput {E = E} {system = system} {tau = tau} C =
  scaledWaveTransversality
    (outputScaleFromP C)
    (C3.modeVector E (Physical.p tau))
    (C3.modeVector E (Physical.k tau))
    (Audit.velocity system (Physical.p tau))
    (outputWaveFromP C)
    (pIncompressible C)

qVelocityTransverseToOutput :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  (C : PhysicalCollinearExtremalData system tau) →
  C3.bilinearDot3
    (C3.modeVector E (Physical.k tau))
    (Audit.velocity system (Physical.q tau))
  ≡ C3.complexZero F
qVelocityTransverseToOutput {E = E} {system = system} {tau = tau} C =
  scaledWaveTransversality
    (outputScaleFromQ C)
    (C3.modeVector E (Physical.q tau))
    (C3.modeVector E (Physical.k tau))
    (Audit.velocity system (Physical.q tau))
    (outputWaveFromQ C)
    (qIncompressible C)

physicalCollinearCrossProjectionZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  (C : PhysicalCollinearExtremalData system tau) →
  C3.lerayProject3 E I (Physical.k tau)
    (Cross.complex3Cross
      (Audit.velocity system (Physical.p tau))
      (Audit.velocity system (Physical.q tau)))
  ≡ C3.complex3Zero F
physicalCollinearCrossProjectionZero {E = E} {I = I}
    {system = system} {tau = tau} C =
  R131.lerayKillsOutputTransverseCross
    E I (Physical.k tau) (outputNonzero C)
    (Audit.velocity system (Physical.p tau))
    (Audit.velocity system (Physical.q tau))
    (pVelocityTransverseToOutput C)
    (qVelocityTransverseToOutput C)

pureCommutatorVectorCollinearZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  (H : R120.PhysicalHelicalOutputPair system tau) →
  (C : PhysicalCollinearExtremalData system tau) →
  R120.pureCommutatorVector system tau H ≡ C3.complex3Zero F
pureCommutatorVectorCollinearZero {system = system} {tau = tau} H C =
  trans
    (cong
      (C3.complex3Scale
        (C3.complexSubtract (R120.signedEigenQ H) (R120.signedEigenP H)))
      (physicalCollinearCrossProjectionZero C))
    (R106.complex3ScaleZeroVector
      (C3.complexSubtract (R120.signedEigenQ H) (R120.signedEigenP H)))

partnerVectorSumCollinearZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  (H : R120.PhysicalHelicalOutputPair system tau) →
  (C : PhysicalCollinearExtremalData system tau) →
  R120.partnerVectorSum system tau ≡ C3.complex3Zero F
partnerVectorSumCollinearZero {system = system} {tau = tau} H C =
  trans
    (R120.sharedOutputPartnerSumIsPureMultiplierDifference system tau H)
    (pureCommutatorVectorCollinearZero H C)

partnerQuarticCellSumCollinearZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  (H : R120.PhysicalHelicalOutputPair system tau) →
  (C : PhysicalCollinearExtremalData system tau) →
  (testCross : C3.Complex3 F) →
  R120.partnerQuarticCellSum system tau testCross ≡ C3.complexZero F
partnerQuarticCellSumCollinearZero {system = system} {tau = tau} H C testCross =
  trans
    (R120.partnerQuarticCellSumIsPureCommutatorPairing system tau H testCross)
    (trans
      (cong (λ forcing → C3.hermitianPairing3 forcing testCross)
        (pureCommutatorVectorCollinearZero H C))
      (Zero.hermitianZeroLeft testCross))

round132PhysicalCollinearTransversalityTransportClosed : Bool
round132PhysicalCollinearTransversalityTransportClosed = true

round132PhysicalCollinearCrossProjectionZeroClosed : Bool
round132PhysicalCollinearCrossProjectionZeroClosed = true

round132CollinearPartnerVectorCancellationClosed : Bool
round132CollinearPartnerVectorCancellationClosed = true

round132CollinearQuarticPartnerCancellationClosed : Bool
round132CollinearQuarticPartnerCancellationClosed = true

round132IntegerCollinearityToScalarWitnessClosed : Bool
round132IntegerCollinearityToScalarWitnessClosed = false

round132IntermediateAngleSignedCriticalPaymentClosed : Bool
round132IntermediateAngleSignedCriticalPaymentClosed = false

round132CriticalHHPaymentClosed : Bool
round132CriticalHHPaymentClosed = false

round132CollinearQuarticPartnerCancellationClosedIsTrue :
  round132CollinearQuarticPartnerCancellationClosed ≡ true
round132CollinearQuarticPartnerCancellationClosedIsTrue = refl

round132IntegerCollinearityToScalarWitnessClosedIsFalse :
  round132IntegerCollinearityToScalarWitnessClosed ≡ false
round132IntegerCollinearityToScalarWitnessClosedIsFalse = refl

round132CriticalHHPaymentClosedIsFalse :
  round132CriticalHHPaymentClosed ≡ false
round132CriticalHHPaymentClosedIsFalse = refl
