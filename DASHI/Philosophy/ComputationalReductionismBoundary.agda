module DASHI.Philosophy.ComputationalReductionismBoundary where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

open import DASHI.Sheaf.GlobalAmbiguityBoundary
  using (GlobalAmbiguity; globalAmbiguityRefutesInjectivity; Injective; ¬_)

------------------------------------------------------------------------
-- Computation is not itself reductionism.
--
-- The strong reductionist step formalised here is observational completeness:
-- treating a selected computable representation as globally lossless, so that
-- equality of codes is enough to conclude equality of underlying states.

record ComputationalRepresentation
    (World Code : Set)
    : Set₁ where
  constructor computationalRepresentation
  field
    encode : World → Code
    representationName : String

open ComputationalRepresentation public

ObservationallyComplete :
  ∀ {World Code : Set} →
  ComputationalRepresentation World Code →
  Set
ObservationallyComplete representation = Injective (encode representation)

record ComputationalReductionistClosure
    {World Code : Set}
    (representation : ComputationalRepresentation World Code)
    : Set₁ where
  field
    observableCodeExhaustsRelevantIdentity : Set
    codeEqualityDeterminesWorldEquality : ObservationallyComplete representation
    contextCanBeDiscarded : Set
    residualCanAlwaysBeEliminated : Set

record SituatedComputationalModel
    (World Code Context Residual : Set)
    : Set₁ where
  constructor situatedComputationalModel
  field
    encodeSituated : World → Context → Code × Residual
    residualMayCarryIdentity : Set
    contextMayChangeInterpretation : Set
    noninjectiveProjectionPermitted : Set

ambiguityRefutesObservationalCompleteness :
  ∀ {World Code : Set}
    (representation : ComputationalRepresentation World Code) →
  GlobalAmbiguity (encode representation) →
  ¬ ObservationallyComplete representation
ambiguityRefutesObservationalCompleteness representation =
  globalAmbiguityRefutesInjectivity

ambiguityRefutesReductionistClosure :
  ∀ {World Code : Set}
    (representation : ComputationalRepresentation World Code) →
  GlobalAmbiguity (encode representation) →
  ¬ ComputationalReductionistClosure representation
ambiguityRefutesReductionistClosure representation ambiguity closure =
  ambiguityRefutesObservationalCompleteness representation ambiguity
    (ComputationalReductionistClosure.codeEqualityDeterminesWorldEquality closure)

------------------------------------------------------------------------
-- A fibre-aware alternative retains the unresolved sheet/index rather than
-- silently identifying states that share a visible code.

record FibreAwareRepresentation
    (World Code Sheet : Set)
    : Set₁ where
  constructor fibreAwareRepresentation
  field
    visibleCode : World → Code
    sheetLabel : World → Sheet
    enrichedCodeInjective : Injective (λ world → visibleCode world , sheetLabel world)

record ReductionismBoundaryReceipt : Set where
  constructor reductionismBoundaryReceipt
  field
    computationEquatedWithReductionism : Bool
    computationEquatedWithReductionismIsFalse :
      computationEquatedWithReductionism ≡ false
    observationalCompletenessNamed : Bool
    globalAmbiguityRefutesLosslessness : Bool
    contextAndResidualRetained : Bool
    allComputableModelsClaimedNoninjective : Bool
    allComputableModelsClaimedNoninjectiveIsFalse :
      allComputableModelsClaimedNoninjective ≡ false
    interpretation : String

reductionismBoundaryReceipt : ReductionismBoundaryReceipt
reductionismBoundaryReceipt =
  reductionismBoundaryReceipt
    false refl
    true true true
    false refl
    "the reductionist move is not computation itself but promoting one computable observation to a globally complete and context-free identity code; GlobalAmbiguity constructively refutes that promotion while leaving injective and fibre-aware computations available"
