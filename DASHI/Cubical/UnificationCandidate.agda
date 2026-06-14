module DASHI.Cubical.UnificationCandidate where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed Cubical adapter compatibility surface.
--
-- The intended Cubical wrapper must import these real receipt variables:
--
--   DASHI.Papers.Unification.TheoremInterface
--     canonicalUnificationPaperTheoremInterface
--     unificationPaperInterfaceTerminalFalse
--     unificationPaperInterfaceUCT4StillOpen
--
--   DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary
--     canonicalUnificationCrossTermNullityTheoremBoundary
--     crossTermNullityTheoremProvedIsFalse
--     terminalPromotionIsFalse
--
--   DASHI.Physics.Closure.UnificationConsumerAuthorityAssemblyBoundary
--     canonicalUnificationConsumerAuthorityAssemblyBoundary
--     TerminalUnificationPromotionEnabled
--
--   DASHI.Promotion.UnificationCriticalPathReceipt
--     canonicalUnificationCriticalPathReceipt
--     canonicalUnificationCriticalPathTerminalPromotionFalse
--
-- A module using --cubical or --erased-cubical cannot import those receipt
-- modules because they were checked without --cubical-compatible and without
-- --without-K.  This module deliberately does not fabricate Cubical paths or
-- terminal unification promotion.

record UnificationCubicalAdapterIncompatibility : Set where
  field
    candidateModule :
      String

    paperInterfaceModule :
      String

    crossTermNullityModule :
      String

    consumerAuthorityModule :
      String

    criticalPathModule :
      String

    requiredExistingVars :
      List String

    exactAgdaIncompatibility :
      List String

    cubicalWrapperConstructed :
      Bool

open UnificationCubicalAdapterIncompatibility public

unificationCubicalAdapterIncompatibility :
  UnificationCubicalAdapterIncompatibility
unificationCubicalAdapterIncompatibility =
  record
    { candidateModule =
        "DASHI.Cubical.UnificationCandidate"
    ; paperInterfaceModule =
        "DASHI.Papers.Unification.TheoremInterface"
    ; crossTermNullityModule =
        "DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary"
    ; consumerAuthorityModule =
        "DASHI.Physics.Closure.UnificationConsumerAuthorityAssemblyBoundary"
    ; criticalPathModule =
        "DASHI.Promotion.UnificationCriticalPathReceipt"
    ; requiredExistingVars =
        "canonicalUnificationPaperTheoremInterface"
        ∷ "unificationPaperInterfaceTerminalFalse"
        ∷ "unificationPaperInterfaceUCT4StillOpen"
        ∷ "canonicalUnificationCrossTermNullityTheoremBoundary"
        ∷ "crossTermNullityTheoremProvedIsFalse"
        ∷ "terminalPromotionIsFalse"
        ∷ "canonicalUnificationConsumerAuthorityAssemblyBoundary"
        ∷ "TerminalUnificationPromotionEnabled"
        ∷ "canonicalUnificationCriticalPathReceipt"
        ∷ "canonicalUnificationCriticalPathTerminalPromotionFalse"
        ∷ []
    ; exactAgdaIncompatibility =
        "Importing DASHI.Papers.Unification.TheoremInterface from a --cubical module fails because the imported module does not use --without-K."
        ∷ "Importing DASHI.Papers.Unification.TheoremInterface from a --cubical module fails because the imported module does not use --cubical-compatible."
        ∷ "The same restriction applies to the underlying Unification closure and promotion receipt modules under --cubical and --erased-cubical."
        ∷ []
    ; cubicalWrapperConstructed =
        false
    }
