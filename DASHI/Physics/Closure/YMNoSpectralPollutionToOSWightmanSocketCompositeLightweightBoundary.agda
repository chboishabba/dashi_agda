module DASHI.Physics.Closure.YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data YMNoSpectralToOSClause : Set where
  noSpectralPollutionSocketImported : YMNoSpectralToOSClause
  reflectionPositivityBoundaryImported : YMNoSpectralToOSClause
  osAxiomConsumerRecorded : YMNoSpectralToOSClause
  osWightmanSocketRecorded : YMNoSpectralToOSClause
  finalMassGapAssemblyStillBlocked : YMNoSpectralToOSClause
  clayPromotionStillBlocked : YMNoSpectralToOSClause

canonicalYMNoSpectralToOSClauses : List YMNoSpectralToOSClause
canonicalYMNoSpectralToOSClauses =
  noSpectralPollutionSocketImported
  ∷ reflectionPositivityBoundaryImported
  ∷ osAxiomConsumerRecorded
  ∷ osWightmanSocketRecorded
  ∷ finalMassGapAssemblyStillBlocked
  ∷ clayPromotionStillBlocked
  ∷ []

ymNoSpectralToOSClauseCount : Nat
ymNoSpectralToOSClauseCount = listLength canonicalYMNoSpectralToOSClauses

ymNoSpectralToOSClauseCountIs6 : ymNoSpectralToOSClauseCount ≡ 6
ymNoSpectralToOSClauseCountIs6 = refl

data YMNoSpectralToOSBlocker : Set where
  blocker-noSpectralPollutionTheoremStillOpen : YMNoSpectralToOSBlocker
  blocker-reflectionPositivityBoundaryStillOpen : YMNoSpectralToOSBlocker
  blocker-osWightmanAuthorityStillOpen : YMNoSpectralToOSBlocker
  blocker-finalAssemblyStillOpen : YMNoSpectralToOSBlocker
  blocker-ymClayPromotionForbidden : YMNoSpectralToOSBlocker

canonicalYMNoSpectralToOSBlockers : List YMNoSpectralToOSBlocker
canonicalYMNoSpectralToOSBlockers =
  blocker-noSpectralPollutionTheoremStillOpen
  ∷ blocker-reflectionPositivityBoundaryStillOpen
  ∷ blocker-osWightmanAuthorityStillOpen
  ∷ blocker-finalAssemblyStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMNoSpectralPollutionToOSWightmanSocketCompositeRecorded : Bool
YMNoSpectralPollutionToOSWightmanSocketCompositeRecorded = true

YMNoSpectralPollutionToOSWightmanSocketCompositeProved : Bool
YMNoSpectralPollutionToOSWightmanSocketCompositeProved = false

record YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary : Set where
  field
    clauses : List YMNoSpectralToOSClause
    clausesCanonical : clauses ≡ canonicalYMNoSpectralToOSClauses
    blockers : List YMNoSpectralToOSBlocker
    blockersCanonical : blockers ≡ canonicalYMNoSpectralToOSBlockers
    clauseCountIs6 : ymNoSpectralToOSClauseCount ≡ 6
    provedStillFalse :
      YMNoSpectralPollutionToOSWightmanSocketCompositeProved ≡ false

canonicalYMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary :
  YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary
canonicalYMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary =
  record
    { clauses = canonicalYMNoSpectralToOSClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMNoSpectralToOSBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

YMNoSpectralPollutionToOSWightmanSocketCompositeRecordedIsTrue :
  YMNoSpectralPollutionToOSWightmanSocketCompositeRecorded ≡ true
YMNoSpectralPollutionToOSWightmanSocketCompositeRecordedIsTrue = refl
