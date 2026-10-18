module DASHI.Physics.YangMills.BalabanClayGate4ProbabilitySemanticCorrectionExact where

------------------------------------------------------------------------
-- SEMANTIC CORRECTION RECEIPT
--
-- The Gate4 T-operation normalizes fast-field reference weights at FIXED slow
-- field.  Therefore that normalized reference object is a conditional kernel
-- slow -> fine, not by itself the global fine marginal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record Gate4ProbabilitySemanticCorrection : Set where
  constructor correction
  field
    normalizedReferenceAsGlobalFineMarginalPreferred : Bool
    normalizedReferenceAsGlobalFineMarginalPreferredIsFalse :
      normalizedReferenceAsGlobalFineMarginalPreferred ≡ false

    normalizedReferenceAsConditionalFastKernelPreferred : Bool
    normalizedReferenceAsConditionalFastKernelPreferredIsTrue :
      normalizedReferenceAsConditionalFastKernelPreferred ≡ true

    fineMarginalDerivedByCoarseMixture : Bool
    fineMarginalDerivedByCoarseMixtureIsTrue :
      fineMarginalDerivedByCoarseMixture ≡ true

    arbitraryReopeningStepStillPreferred : Bool
    arbitraryReopeningStepStillPreferredIsFalse :
      arbitraryReopeningStepStillPreferred ≡ false

canonicalGate4ProbabilitySemanticCorrection :
  Gate4ProbabilitySemanticCorrection
canonicalGate4ProbabilitySemanticCorrection =
  correction false refl true refl true refl false refl
