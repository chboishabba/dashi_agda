module DASHI.MDL.MultiscaleCodingTargets where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Nat using (_≤_)

open import DASHI.Core.MultiscaleMDL
open import DASHI.MDL.MDLLyapunov

multiscaleMDLFunctional :
  ∀ {tower : MultiscaleCarrier}
    {codec : ResidualCodec tower}
    (cost : MDLCost tower codec)
    (j : Nat) →
  MDLFunctional (Carrier tower (suc j))
multiscaleMDLFunctional {tower} {codec} cost j =
  record
    { model = λ x → coarseCost cost (project tower x)
    ; residual = λ x → residualCost cost (residual codec x)
    ; mdl = stepDescriptionLength cost
    ; mdl≡ = λ _ → refl
    }

record SourceCodingModel (Symbol : Set) : Set₁ where
  field
    sourceWeight : Symbol → Nat
    codeLength : Symbol → Nat
    uniquelyDecodable : Set
    kraftAdmissible : Set
    entropyLowerBound : Set
    expectedLengthUpperBound : Set
open SourceCodingModel public

record DistortionModel (Source Reconstruction : Set) : Set₁ where
  field
    distortion : Source → Reconstruction → Nat
    budget : Nat
    admissibleReconstruction : Source → Reconstruction → Set
open DistortionModel public

record RateDistortionReceipt
  {Source Reconstruction : Set}
  (D : DistortionModel Source Reconstruction) : Set₁ where
  field
    candidateRate : Nat
    baselineRate : Nat
    candidateMeetsBudget : Set
    baselineMeetsBudget : Set
    candidateNoWorse : candidateRate ≤ baselineRate
    sourceModelDeclared : Set
    sideInformationAccounted : Set
open RateDistortionReceipt public

record MultiscaleCodingTheoremTarget
  {tower : MultiscaleCarrier}
  (codec : ResidualCodec tower)
  (cost : MDLCost tower codec) : Set₁ where
  field
    residualSourceModel : ∀ j → SourceCodingModel (Residual codec j)
    exactDecoderAlreadySupplied :
      ∀ {j} (x : Carrier tower (suc j)) →
      reconstruct codec (project tower x) (residual codec x) ≡ x
    residualEntropyTheorem : Set
    finitePrecisionCoderCorrect : Set
    rateDistortionTheorem : Set
open MultiscaleCodingTheoremTarget public

exact-decoder-from-codec :
  ∀ {tower : MultiscaleCarrier}
    (codec : ResidualCodec tower)
    {j} (x : Carrier tower (suc j)) →
  reconstruct codec (project tower x) (residual codec x) ≡ x
exact-decoder-from-codec codec x = reconstruct-project-residual codec x
