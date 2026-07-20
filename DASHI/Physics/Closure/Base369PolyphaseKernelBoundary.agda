module DASHI.Physics.Closure.Base369PolyphaseKernelBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth
  ; tri-mid
  ; rotateTri
  )
open import DASHI.Foundations.Base369TriTruthField using
  ( triAdd
  ; triOne
  )
open import DASHI.Foundations.Base369PolyphaseCharacters using
  ( C3Sequence
  ; zeroSequence
  ; positiveSequence
  ; negativeSequence
  ; characterExponent3
  ; characterExponent3-additive
  )

------------------------------------------------------------------------
-- A finite equivariant-kernel contract.

record EquivariantPolyphaseKernel (Phase : Set) : Set where
  constructor mkEquivariantPolyphaseKernel
  field
    shift : Phase → Phase
    kernel : Phase → Phase
    commutesWithShift :
      (x : Phase) →
      kernel (shift x) ≡ shift (kernel x)

open EquivariantPolyphaseKernel public

identityC3Kernel : EquivariantPolyphaseKernel TriTruth
identityC3Kernel =
  mkEquivariantPolyphaseKernel
    rotateTri
    (λ x → x)
    (λ x → refl)

rotationC3Kernel : EquivariantPolyphaseKernel TriTruth
rotationC3Kernel =
  mkEquivariantPolyphaseKernel
    rotateTri
    rotateTri
    (λ x → refl)

------------------------------------------------------------------------
-- Character-sector response to one positive phase step.
--
-- This is the exponent form of the usual character eigen-relation:
-- shifting the phase adds the mode's one-step exponent.  No complex
-- scalar eigenvalue is claimed here.

oneStepPhase : TriTruth → TriTruth
oneStepPhase phase = triAdd triOne phase

characterOneStepLaw :
  (mode : C3Sequence) →
  (phase : TriTruth) →
  characterExponent3 mode (oneStepPhase phase) ≡
  triAdd
    (characterExponent3 mode triOne)
    (characterExponent3 mode phase)
characterOneStepLaw mode phase =
  characterExponent3-additive mode triOne phase

record C3KernelModeReceipt : Set where
  constructor mkC3KernelModeReceipt
  field
    mode : C3Sequence
    phaseKernel : EquivariantPolyphaseKernel TriTruth
    oneStepResponse :
      (phase : TriTruth) →
      characterExponent3 mode (oneStepPhase phase) ≡
      triAdd
        (characterExponent3 mode triOne)
        (characterExponent3 mode phase)

c3KernelModeReceipt : C3Sequence → C3KernelModeReceipt
c3KernelModeReceipt mode =
  mkC3KernelModeReceipt
    mode
    rotationC3Kernel
    (characterOneStepLaw mode)

zeroSequenceKernelReceipt : C3KernelModeReceipt
zeroSequenceKernelReceipt = c3KernelModeReceipt zeroSequence

positiveSequenceKernelReceipt : C3KernelModeReceipt
positiveSequenceKernelReceipt = c3KernelModeReceipt positiveSequence

negativeSequenceKernelReceipt : C3KernelModeReceipt
negativeSequenceKernelReceipt = c3KernelModeReceipt negativeSequence

------------------------------------------------------------------------
-- Resonance and spectral-authority gate.

record PolyphaseSpectralBoundary : Set where
  constructor mkPolyphaseSpectralBoundary
  field
    finiteShiftEquivarianceChecked : Bool
    symbolicCharacterStepLawChecked : Bool
    complexEigenvalueDiagonalisationPromoted : Bool
    complexEigenvalueDiagonalisationPromotedIsFalse :
      complexEigenvalueDiagonalisationPromoted ≡ false
    physicalResonancePromoted : Bool
    physicalResonancePromotedIsFalse :
      physicalResonancePromoted ≡ false
    forcingOverlapMeasured : Bool
    forcingOverlapMeasuredIsFalse :
      forcingOverlapMeasured ≡ false
    boundary : String

polyphaseSpectralBoundary : PolyphaseSpectralBoundary
polyphaseSpectralBoundary =
  mkPolyphaseSpectralBoundary
    true
    true
    false
    refl
    false
    refl
    false
    refl
    "Finite C3 shift equivariance and symbolic character response are checked. Complex diagonalisation, measured forcing overlap, damping/amplification, stability boundaries, and physical resonance remain external analytic/empirical obligations."
