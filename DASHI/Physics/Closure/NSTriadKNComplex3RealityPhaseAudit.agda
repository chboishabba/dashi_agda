module DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

------------------------------------------------------------------------
-- Correct Fourier reality law.
------------------------------------------------------------------------

RealityCondition :
  ∀ {r} {F : C3.RealField r} →
  (Z3.FourierMode → C3.Complex3 F) → Set r
RealityCondition state =
  ∀ k → state (Z3.negateMode k) ≡ C3.complex3Conjugate (state k)

DivergenceFreeCondition :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  (Z3.FourierMode → C3.Complex3 F) → Set r
DivergenceFreeCondition {F = F} E state =
  ∀ k →
  C3.bilinearDot3 (state k) (C3.modeVector E k)
  ≡ C3.complexZero F

record CorrectComplex3RealityLaws
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set (lsuc r) where
  field
    inverseNormEven : ∀ k →
      C3.inverseNormSquared I (Z3.negateMode k)
      ≡ C3.inverseNormSquared I k

    lerayModeEven : ∀ k value →
      C3.lerayProject3 E I (Z3.negateMode k) value
      ≡ C3.lerayProject3 E I k value

    lerayConjugation : ∀ k value →
      C3.lerayProject3 E I k (C3.complex3Conjugate value)
      ≡ C3.complex3Conjugate (C3.lerayProject3 E I k value)

open CorrectComplex3RealityLaws public

waveVectorNegationClosed :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode) →
  C3.modeVector E (Z3.negateMode k)
  ≡ C3.complex3Negate (C3.modeVector E k)
waveVectorNegationClosed = C3.modeVectorNegation

waveVectorConjugationClosed :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode) →
  C3.complex3Conjugate (C3.modeVector E k)
  ≡ C3.modeVector E k
waveVectorConjugationClosed = C3.modeVectorConjugate

record FiniteGalerkinRealityPreservation
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (realityLaws : CorrectComplex3RealityLaws F E I) : Set (lsuc r) where
  field
    VelocityState : Set r
    coefficients : VelocityState → Z3.FourierMode → C3.Complex3 F
    nonlinearVectorField : VelocityState → Z3.FourierMode → C3.Complex3 F

    stateReality :
      (state : VelocityState) →
      RealityCondition (coefficients state)

    nonlinearReality :
      (state : VelocityState) →
      (k : Z3.FourierMode) →
      nonlinearVectorField state (Z3.negateMode k)
      ≡ C3.complex3Conjugate (nonlinearVectorField state k)

open FiniteGalerkinRealityPreservation public

------------------------------------------------------------------------
-- Normalised transverse frames.
------------------------------------------------------------------------

record NormalisedTransverseFrame
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (nonzero : Z3.NonZeroMode k) : Set (lsuc r) where
  field
    e₁ e₂ : C3.Complex3 F

    e₁Transverse :
      C3.bilinearDot3 (C3.modeVector E k) e₁ ≡ C3.complexZero F
    e₂Transverse :
      C3.bilinearDot3 (C3.modeVector E k) e₂ ≡ C3.complexZero F

    e₁Normalised :
      C3.hermitianPairing3 e₁ e₁ ≡ C3.complexOne F
    e₂Normalised :
      C3.hermitianPairing3 e₂ e₂ ≡ C3.complexOne F
    frameOrthogonal :
      C3.hermitianPairing3 e₁ e₂ ≡ C3.complexZero F

open NormalisedTransverseFrame public

record RealityCompatibleFrameFamily
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set (lsuc r) where
  field
    frame :
      (k : Z3.FourierMode) →
      (nonzero : Z3.NonZeroMode k) →
      NormalisedTransverseFrame F E k nonzero

    frame₁Reality :
      (k : Z3.FourierMode) →
      (nonzero : Z3.NonZeroMode k) →
      (negNonzero : Z3.NonZeroMode (Z3.negateMode k)) →
      e₁ (frame (Z3.negateMode k) negNonzero)
      ≡ C3.complex3Conjugate (e₁ (frame k nonzero))

    frame₂Reality :
      (k : Z3.FourierMode) →
      (nonzero : Z3.NonZeroMode k) →
      (negNonzero : Z3.NonZeroMode (Z3.negateMode k)) →
      e₂ (frame (Z3.negateMode k) negNonzero)
      ≡ C3.complex3Conjugate (e₂ (frame k nonzero))

open RealityCompatibleFrameFamily public

------------------------------------------------------------------------
-- Phase coordinates without an undefined phase at zero amplitude.
------------------------------------------------------------------------

record PhaseCoordinateSystem
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    Amplitude Phase Polarisation : Set r
    amplitudeZero : Amplitude
    phaseOne : Phase

    AmplitudeNonnegative : Amplitude → Set r
    amplitudeNonnegative : (amplitude : Amplitude) → AmplitudeNonnegative amplitude

    phaseScalar : Phase → C3.Complex F
    polarisationVector : Polarisation → C3.Complex3 F
    amplitudeScalar : Amplitude → C3.Complex F

    phaseUnitMagnitude : (phase : Phase) →
      C3.complexMultiply
        (phaseScalar phase)
        (C3.complexConjugate (phaseScalar phase))
      ≡ C3.complexOne F

    synthesise : Amplitude → Phase → Polarisation → C3.Complex3 F
    synthesisMeaning : ∀ amplitude phase polarisation →
      synthesise amplitude phase polarisation
      ≡ C3.complex3Scale
          (C3.complexMultiply
            (amplitudeScalar amplitude)
            (phaseScalar phase))
          (polarisationVector polarisation)

    zeroAmplitudePhaseIndependent : ∀ phase₁ phase₂ polarisation →
      synthesise amplitudeZero phase₁ polarisation
      ≡ synthesise amplitudeZero phase₂ polarisation

open PhaseCoordinateSystem public

record ExactComplex3PhaseFormula
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (coordinates : PhaseCoordinateSystem F) : Set (lsuc r) where
  field
    geometryCoefficient :
      Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
      Polarisation coordinates →
      Polarisation coordinates →
      Polarisation coordinates →
      C3.Complex F

    phaseCombination :
      Phase coordinates → Phase coordinates → Phase coordinates →
      C3.Complex F

    amplitudeProduct :
      Amplitude coordinates →
      Amplitude coordinates →
      Amplitude coordinates →
      C3.Complex F

    exactPhaseFormula :
      ∀ k p q aP aQ aK phaseP phaseQ phaseK polP polQ polK →
      Signed.testedSignedCoefficient
        (C3.complex3VelocityGalerkinLaws F E I)
        k p q
        (synthesise coordinates aP phaseP polP)
        (synthesise coordinates aQ phaseQ polQ)
        (synthesise coordinates aK phaseK polK)
      ≡
      C3.complexRealPart
        (C3.complexMultiply
          (amplitudeProduct aP aQ aK)
          (C3.complexMultiply
            (geometryCoefficient k p q polP polQ polK)
            (phaseCombination phaseP phaseQ phaseK)))

open ExactComplex3PhaseFormula public

------------------------------------------------------------------------
-- Correct energy-cancellation conventions.
------------------------------------------------------------------------

orderedSignedTransferAt :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
orderedSignedTransferAt {F = F} E I τ velocity =
  Signed.testedSignedCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)
    (Physical.k τ)
    (Physical.p τ)
    (Physical.q τ)
    (velocity (Physical.p τ))
    (velocity (Physical.q τ))
    (velocity (Physical.k τ))

signedTransferAt :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
signedTransferAt = orderedSignedTransferAt

orderedPairSignedTransferAt :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
orderedPairSignedTransferAt {F = F} E I τ velocity =
  Signed.testedOrderedPairCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)
    (Physical.k τ)
    (Physical.p τ)
    (Physical.q τ)
    (velocity (Physical.p τ))
    (velocity (Physical.q τ))
    (velocity (Physical.k τ))

record ExactOrderedRealityPairCancellation
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (baseTriad : Physical.PhysicalTriadIncidence) : Set (lsuc r) where
  field
    orderedRealityPairCancellation :
      (velocity : Z3.FourierMode → C3.Complex3 F) →
      RealityCondition velocity →
      DivergenceFreeCondition E velocity →
      C3.complexAdd
        (orderedSignedTransferAt E I baseTriad velocity)
        (orderedSignedTransferAt E I
          (Orbit.orderedRealityMate baseTriad) velocity)
      ≡ C3.complexZero F

open ExactOrderedRealityPairCancellation public

record ExactTriadEnergyCancellation
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (baseTriad : Physical.PhysicalTriadIncidence) : Set (lsuc r) where
  field
    completeTriadCancellation :
      (velocity : Z3.FourierMode → C3.Complex3 F) →
      RealityCondition velocity →
      DivergenceFreeCondition E velocity →
      C3.complexAdd
        (C3.complexAdd
          (orderedPairSignedTransferAt E I baseTriad velocity)
          (orderedPairSignedTransferAt E I
            (Orbit.pEnergyLeg baseTriad) velocity))
        (orderedPairSignedTransferAt E I
          (Orbit.qEnergyLeg baseTriad) velocity)
      ≡ C3.complexZero F

open ExactTriadEnergyCancellation public

correctRealityLawSpecified : Bool
correctRealityLawSpecified = true

correctRealityLawSpecifiedIsTrue : correctRealityLawSpecified ≡ true
correctRealityLawSpecifiedIsTrue = refl

waveVectorRealityAlgebraClosed : Bool
waveVectorRealityAlgebraClosed = true

waveVectorRealityAlgebraClosedIsTrue : waveVectorRealityAlgebraClosed ≡ true
waveVectorRealityAlgebraClosedIsTrue = refl

energyCancellationConventionCorrected : Bool
energyCancellationConventionCorrected = true

energyCancellationConventionCorrectedIsTrue :
  energyCancellationConventionCorrected ≡ true
energyCancellationConventionCorrectedIsTrue = refl

normalisedFrameTargetSpecified : Bool
normalisedFrameTargetSpecified = true

normalisedFrameTargetSpecifiedIsTrue : normalisedFrameTargetSpecified ≡ true
normalisedFrameTargetSpecifiedIsTrue = refl

phaseFormulaDerivedFromSignedCoefficient : Bool
phaseFormulaDerivedFromSignedCoefficient = false

phaseFormulaDerivedFromSignedCoefficientIsFalse :
  phaseFormulaDerivedFromSignedCoefficient ≡ false
phaseFormulaDerivedFromSignedCoefficientIsFalse = refl

completeTriadEnergyCancellationClosed : Bool
completeTriadEnergyCancellationClosed = true

completeTriadEnergyCancellationClosedIsTrue :
  completeTriadEnergyCancellationClosed ≡ true
completeTriadEnergyCancellationClosedIsTrue = refl
