module DASHI.Biology.SymbolicTransformWithoutHomunculus where

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as Stateful

------------------------------------------------------------------------
-- Symbolic transformation without an inner symbolic translator.
--
-- A transformed rendering may preserve a latent invariant while changing the
-- local carrier and lowering an access cost.  The theorem says only that such
-- a structural transformation is possible; it does not install a universal
-- dream dictionary or infer hidden personal content from a symbol.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data SymbolForm : Set where
  directForm : Bool → SymbolForm
  transformedForm : Bool → SymbolForm

symbolInvariant : SymbolForm → Bool
symbolInvariant (directForm content) = content
symbolInvariant (transformedForm content) = content

directRender : Bool → SymbolForm
directRender latent = directForm latent

transformedRender : Bool → SymbolForm
transformedRender latent = transformedForm latent

renderingInvariantPreservedDirect :
  (latent : Bool) →
  symbolInvariant (directRender latent) ≡ latent
renderingInvariantPreservedDirect latent = refl

renderingInvariantPreservedTransformed :
  (latent : Bool) →
  symbolInvariant (transformedRender latent) ≡ latent
renderingInvariantPreservedTransformed latent = refl

directAndTransformedCarriersDifferAtTrue :
  directRender true ≢ transformedRender true
directAndTransformedCarriersDifferAtTrue ()

record SymbolicCompromise : Set₁ where
  field
    Latent : Set
    Symbol : Set

    direct : Latent → Symbol
    transformed : Latent → Symbol

    LatentInvariant : Latent → Set
    SymbolInvariant : Symbol → Set

    directPreservesInvariant :
      (z : Latent) →
      LatentInvariant z →
      SymbolInvariant (direct z)

    transformedPreservesInvariant :
      (z : Latent) →
      LatentInvariant z →
      SymbolInvariant (transformed z)

    directAccessCost : Nat
    transformedAccessCost : Nat

    transformedCostNoGreater :
      transformedAccessCost ≤ directAccessCost

    innerTranslatorRequired : Bool
    innerTranslatorRequiredIsFalse :
      innerTranslatorRequired ≡ false

open SymbolicCompromise public

TrueInvariant : Bool → Set
TrueInvariant true = ⊤
TrueInvariant false = ⊥

SymbolTrueInvariant : SymbolForm → Set
SymbolTrueInvariant symbol =
  TrueInvariant (symbolInvariant symbol)

canonicalSymbolicCompromise : SymbolicCompromise
canonicalSymbolicCompromise =
  record
    { Latent = Bool
    ; Symbol = SymbolForm
    ; direct = directRender
    ; transformed = transformedRender
    ; LatentInvariant = TrueInvariant
    ; SymbolInvariant = SymbolTrueInvariant
    ; directPreservesInvariant = λ z proof → proof
    ; transformedPreservesInvariant = λ z proof → proof
    ; directAccessCost = suc (suc zero)
    ; transformedAccessCost = suc zero
    ; transformedCostNoGreater = s≤s z≤n
    ; innerTranslatorRequired = false
    ; innerTranslatorRequiredIsFalse = refl
    }

canonicalTrueLatentHasTransformedInvariant :
  SymbolInvariant canonicalSymbolicCompromise
    (transformed canonicalSymbolicCompromise true)
canonicalTrueLatentHasTransformedInvariant =
  transformedPreservesInvariant canonicalSymbolicCompromise true tt

------------------------------------------------------------------------
-- Condensation: distinct latent inputs may map to one rendering.

condense : Bool → SymbolForm
condense _ = transformedForm false

condensationEqual :
  condense false ≡ condense true
condensationEqual = refl

condensedInputsRemainDistinct : false ≢ true
condensedInputsRemainDistinct = Stateful.false≢true

record SymbolicTransformBoundary : Set where
  constructor symbolicTransformBoundary
  field
    symbolHasFixedUniversalMeaning : Bool
    symbolHasFixedUniversalMeaningIsFalse :
      symbolHasFixedUniversalMeaning ≡ false

    symbolRecoversHiddenMemory : Bool
    symbolRecoversHiddenMemoryIsFalse :
      symbolRecoversHiddenMemory ≡ false

    transformedCarrierErasesAllStructure : Bool
    transformedCarrierErasesAllStructureIsFalse :
      transformedCarrierErasesAllStructure ≡ false

    psychoanalyticAuthorityPromoted : Bool
    psychoanalyticAuthorityPromotedIsFalse :
      psychoanalyticAuthorityPromoted ≡ false

canonicalSymbolicTransformBoundary : SymbolicTransformBoundary
canonicalSymbolicTransformBoundary =
  symbolicTransformBoundary
    false refl
    false refl
    false refl
    false refl
