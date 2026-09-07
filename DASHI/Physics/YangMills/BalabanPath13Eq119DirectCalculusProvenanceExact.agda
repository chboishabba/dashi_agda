{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119DirectCalculusProvenanceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13DirectCalculusSourceFamilyExact as Direct
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredDirectCalculusSourceFamilyExact as Preferred

record DirectCalculusSourceCutStatus : Set where
  field
    directR159SourceCompilerClosed : Bool
    historicalR177CompatibilityClosed : Bool
    preferredRouteRequiresR177Family : Bool
    preferredRouteRequiresUniformCalculus : Bool
    preferredRouteRequiresIndependentNativeRadius : Bool
    preferredRouteRequiresIndependentR208Embedding : Bool
    physicalEquation119Closed : Bool

    directR159SourceCompilerClosedIsTrue : directR159SourceCompilerClosed ≡ true
    historicalR177CompatibilityClosedIsTrue : historicalR177CompatibilityClosed ≡ true
    preferredRouteRequiresR177FamilyIsFalse : preferredRouteRequiresR177Family ≡ false
    preferredRouteRequiresUniformCalculusIsTrue : preferredRouteRequiresUniformCalculus ≡ true
    preferredRouteRequiresIndependentNativeRadiusIsFalse :
      preferredRouteRequiresIndependentNativeRadius ≡ false
    preferredRouteRequiresIndependentR208EmbeddingIsFalse :
      preferredRouteRequiresIndependentR208Embedding ≡ false
    physicalEquation119ClosedIsFalse : physicalEquation119Closed ≡ false
open DirectCalculusSourceCutStatus public

canonicalDirectCalculusSourceCutStatus : DirectCalculusSourceCutStatus
canonicalDirectCalculusSourceCutStatus = record
  { directR159SourceCompilerClosed = true
  ; historicalR177CompatibilityClosed = true
  ; preferredRouteRequiresR177Family = false
  ; preferredRouteRequiresUniformCalculus = true
  ; preferredRouteRequiresIndependentNativeRadius = false
  ; preferredRouteRequiresIndependentR208Embedding = false
  ; physicalEquation119Closed = false
  ; directR159SourceCompilerClosedIsTrue = refl
  ; historicalR177CompatibilityClosedIsTrue = refl
  ; preferredRouteRequiresR177FamilyIsFalse = refl
  ; preferredRouteRequiresUniformCalculusIsTrue = refl
  ; preferredRouteRequiresIndependentNativeRadiusIsFalse = refl
  ; preferredRouteRequiresIndependentR208EmbeddingIsFalse = refl
  ; physicalEquation119ClosedIsFalse = refl
  }

r177CompatibilityDoesNotMakeR177Primitive :
  historicalR177CompatibilityClosed canonicalDirectCalculusSourceCutStatus ≡ true
r177CompatibilityDoesNotMakeR177Primitive = refl

r177NotPreferredPayment :
  preferredRouteRequiresR177Family canonicalDirectCalculusSourceCutStatus ≡ false
r177NotPreferredPayment = refl

uniformCalculusIsPreferredPayment :
  preferredRouteRequiresUniformCalculus canonicalDirectCalculusSourceCutStatus ≡ true
uniformCalculusIsPreferredPayment = refl

physicalClosureStillOpen :
  physicalEquation119Closed canonicalDirectCalculusSourceCutStatus ≡ false
physicalClosureStillOpen = refl

cmp98Path13DirectCalculusProvenanceLevel : ProofLevel
cmp98Path13DirectCalculusProvenanceLevel = machineChecked

directSourceCompilerLevel : ProofLevel
directSourceCompilerLevel = Direct.cmp98Path13DirectCalculusSourceFamilyLevel

preferredSourceAdapterLevel : ProofLevel
preferredSourceAdapterLevel = Preferred.cmp98Path13PreferredDirectCalculusAdapterLevel
