module DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

------------------------------------------------------------------------
-- Correct Fourier reality law.
--
-- For a real velocity field, u(-k) = conjugate (u(k)).  The literal wave
-- vector itself obeys q(-k) = -q(k), not q(-k) = conjugate(q(k)).
------------------------------------------------------------------------

RealityCondition :
  ∀ {r} {F : C3.RealField r} →
  (Z3.FourierMode → C3.Complex3 F) → Set r
RealityCondition state =
  ∀ k → state (Z3.negateMode k) ≡ C3.complex3Conjugate (state k)

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
-- Normalised transverse frames.  A frame is data plus proofs, not an
-- arbitrary choice hidden behind a code-to-mode authority.
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
-- Complete triad energy cancellation tied to the exact signed coefficient.
------------------------------------------------------------------------

signedTransferAt :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
signedTransferAt {F = F} E I τ velocity =
  Signed.testedSignedCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)
    (Physical.k τ)
    (Physical.p τ)
    (Physical.q τ)
    (velocity (Physical.p τ))
    (velocity (Physical.q τ))
    (velocity (Physical.k τ))

record ExactTriadEnergyCancellation
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set (lsuc r) where
  field
    baseTriad legK legP legQ : Physical.PhysicalTriadIncidence

    legKIsBase : legK ≡ baseTriad

    pLegFirstInput : Physical.p legP ≡ Physical.k baseTriad
    pLegSecondInput :
      Physical.q legP ≡ Z3.negateMode (Physical.q baseTriad)
    pLegOutput : Physical.k legP ≡ Physical.p baseTriad

    qLegFirstInput : Physical.p legQ ≡ Physical.k baseTriad
    qLegSecondInput :
      Physical.q legQ ≡ Z3.negateMode (Physical.p baseTriad)
    qLegOutput : Physical.k legQ ≡ Physical.q baseTriad

    completeTriadCancellation :
      (velocity : Z3.FourierMode → C3.Complex3 F) →
      RealityCondition velocity →
      C3.complexAdd
        (C3.complexAdd
          (signedTransferAt E I legK velocity)
          (signedTransferAt E I legP velocity))
        (signedTransferAt E I legQ velocity)
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
completeTriadEnergyCancellationClosed = false

completeTriadEnergyCancellationClosedIsFalse :
  completeTriadEnergyCancellationClosed ≡ false
completeTriadEnergyCancellationClosedIsFalse = refl
