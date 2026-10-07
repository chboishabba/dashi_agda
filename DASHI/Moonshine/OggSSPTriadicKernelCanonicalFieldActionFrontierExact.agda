module DASHI.Moonshine.OggSSPTriadicKernelCanonicalFieldActionFrontierExact where

------------------------------------------------------------------------
-- CANONICAL FIELD-ACTION FRONTIER FOR THE TRIADIC KERNELS
--
-- The canonical codec plus the Heisenberg bridge now anchor the additive
-- F3-structure independently.  A selected extension-field product exists and
-- is exhaustively verified, but the paid additive/negation structure does not
-- determine it uniquely: swapping two coordinates is an exact automorphism of
-- addition and inversion, while runtime conjugation through that automorphism
-- changes the chosen multiplication in degrees 4,5,6.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.OggSSPTriadicKernelF3LinearExact as Linear
import DASHI.Moonshine.Generated.OggSSPKernelFieldRecognitionGenerated as Generated
import DASHI.Moonshine.Generated.OggSSPMaxCutRuntimeGenerated as Runtime

open Codec using ([]ᵥ; _∷ᵥ_)

record CanonicalFieldActionSocket (d : Nat) : Set₁ where
  field
    one : Codec.Kernel d
    multiply : Codec.Kernel d → Codec.Kernel d → Codec.Kernel d
    frobenius : Codec.Kernel d → Codec.Kernel d

    minusOneActsAsExistingInversion :
      (x : Codec.Kernel d) →
      multiply (Linear.scaleKernel Trit.neg one) x ≡ Codec.invertKernel x

    frobeniusPreservesMultiply :
      (x y : Codec.Kernel d) →
      frobenius (multiply x y) ≡ multiply (frobenius x) (frobenius y)

    frobeniusPreservesAdd :
      (x y : Codec.Kernel d) →
      frobenius (Linear.addKernel x y)
      ≡ Linear.addKernel (frobenius x) (frobenius y)

K4CanonicalFieldAction : Set₁
K4CanonicalFieldAction = CanonicalFieldActionSocket 4

K5CanonicalFieldAction : Set₁
K5CanonicalFieldAction = CanonicalFieldActionSocket 5

K6CanonicalFieldAction : Set₁
K6CanonicalFieldAction = CanonicalFieldActionSocket 6

------------------------------------------------------------------------
-- Exact additive/inversion automorphism on K4.
------------------------------------------------------------------------

swap01K4 : Linear.Kernel4 → Linear.Kernel4
swap01K4 (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ) =
  b ∷ᵥ a ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ

swap01K4Involutive :
  (x : Linear.Kernel4) → swap01K4 (swap01K4 x) ≡ x
swap01K4Involutive (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ) = refl

swap01K4PreservesAddition :
  (x y : Linear.Kernel4) →
  swap01K4 (Linear.addKernel x y)
  ≡ Linear.addKernel (swap01K4 x) (swap01K4 y)
swap01K4PreservesAddition
  (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ)
  (e ∷ᵥ f ∷ᵥ g ∷ᵥ h ∷ᵥ []ᵥ) = refl

swap01K4PreservesExistingInversion :
  (x : Linear.Kernel4) →
  swap01K4 (Codec.invertKernel x)
  ≡ Codec.invertKernel (swap01K4 x)
swap01K4PreservesExistingInversion
  (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ) = refl

runtimeK4SwapPreservesAddNeg :
  Runtime.k4CoordinateSwapPreservesAddNeg ≡ true
runtimeK4SwapPreservesAddNeg = refl

runtimeK4SwapChangesChosenMultiplication :
  Runtime.k4CoordinateSwapChangesChosenMultiplication ≡ true
runtimeK4SwapChangesChosenMultiplication = refl

runtimeK5SwapChangesChosenMultiplication :
  Runtime.k5CoordinateSwapChangesChosenMultiplication ≡ true
runtimeK5SwapChangesChosenMultiplication = refl

runtimeK6SwapChangesChosenMultiplication :
  Runtime.k6CoordinateSwapChangesChosenMultiplication ≡ true
runtimeK6SwapChangesChosenMultiplication = refl

------------------------------------------------------------------------
-- Interpretation of the no-go.
--
-- The witness proves that the currently paid additive + global-negation data
-- does not single out the selected multiplication.  It does NOT prove that no
-- richer independently existing DASHI action can do so; that richer action is
-- precisely what the socket above requests.
------------------------------------------------------------------------

record CanonicalFieldActionFrontierBoundary : Set where
  constructor canonical-field-action-frontier-boundary
  field
    coordinateF3VectorSpacePaid : Bool
    chosenExtensionFieldRuntimePaid : Bool
    existingInversionMinusOneWeldPaid : Bool
    chosenK4GF9SubfieldMapPaid : Bool
    additiveNegationStructureSelectsChosenMultiplication : Bool
    explicitAdditiveSymmetryChangesChosenMultiplication : Bool
    canonicalMultiplicationFromRicherPriorActionPaid : Bool
    canonicalFrobeniusFromRicherPriorActionPaid : Bool
    fullFieldActionRecognitionPaid : Bool

canonicalFieldActionFrontierBoundary : CanonicalFieldActionFrontierBoundary
canonicalFieldActionFrontierBoundary =
  canonical-field-action-frontier-boundary
    true
    Generated.chosenFieldMultiplicationRuntimeVerified
    true
    Generated.k4T5ChosenSubfieldObjectMapPaid
    false
    Runtime.k4CoordinateSwapChangesChosenMultiplication
    false false false
