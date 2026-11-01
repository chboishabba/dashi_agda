module DASHI.Cubical.YangMillsCandidate where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed Cubical adapter compatibility surface.
--
-- The intended Cubical wrapper must import these real receipt variables:
--
--   DASHI.Physics.Closure.YMMassGapSurvivalAuthority
--     massGapSurvivalAuthorityConditional
--     massGapSurvivalAuthorityBoundary
--     clayYangMillsCandidateAuthorityConditional
--
--   DASHI.Physics.Closure.YMClayPromotionBoundary
--     clayPromotionBoundary
--     clayYangMillsPromoted
--     clayYangMillsPromotedAuthorityConditional
--
-- A module using --cubical or --erased-cubical cannot import those receipt
-- modules because they were checked without --cubical-compatible and without
-- --without-K.  This module deliberately does not fabricate Cubical paths.

record YangMillsCubicalAdapterIncompatibility : Set where
  field
    candidateModule :
      String

    survivalReceiptModule :
      String

    promotionBoundaryModule :
      String

    requiredExistingVars :
      List String

    exactAgdaIncompatibility :
      List String

    cubicalWrapperConstructed :
      Bool

open YangMillsCubicalAdapterIncompatibility public

yangMillsCubicalAdapterIncompatibility :
  YangMillsCubicalAdapterIncompatibility
yangMillsCubicalAdapterIncompatibility =
  record
    { candidateModule =
        "DASHI.Cubical.YangMillsCandidate"
    ; survivalReceiptModule =
        "DASHI.Physics.Closure.YMMassGapSurvivalAuthority"
    ; promotionBoundaryModule =
        "DASHI.Physics.Closure.YMClayPromotionBoundary"
    ; requiredExistingVars =
        "massGapSurvivalAuthorityConditional"
        ∷ "massGapSurvivalAuthorityBoundary"
        ∷ "clayYangMillsCandidateAuthorityConditional"
        ∷ "clayPromotionBoundary"
        ∷ "clayYangMillsPromoted"
        ∷ "clayYangMillsPromotedAuthorityConditional"
        ∷ []
    ; exactAgdaIncompatibility =
        "Importing DASHI.Physics.Closure.YMMassGapSurvivalAuthority from a --cubical module fails because the imported module does not use --without-K."
        ∷ "Importing DASHI.Physics.Closure.YMMassGapSurvivalAuthority from a --cubical module fails because the imported module does not use --cubical-compatible."
        ∷ "The same restriction applies under --erased-cubical."
        ∷ []
    ; cubicalWrapperConstructed =
        false
    }
