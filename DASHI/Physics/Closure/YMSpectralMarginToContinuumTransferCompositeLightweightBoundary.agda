module DASHI.Physics.Closure.YMSpectralMarginToContinuumTransferCompositeLightweightBoundary where

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

data YMSpectralContinuumClause : Set where
  spectralMarginRouteImported : YMSpectralContinuumClause
  h3aPrincipalIntakeSocketImported : YMSpectralContinuumClause
  h3bDownstreamSocketImported : YMSpectralContinuumClause
  finiteVolumeToBulkGapRecorded : YMSpectralContinuumClause
  rgResidualHonestyRetained : YMSpectralContinuumClause
  noSpectralPollutionDependsOnH3aH3b : YMSpectralContinuumClause
  osWightmanSocketRecorded : YMSpectralContinuumClause

canonicalYMSpectralContinuumClauses : List YMSpectralContinuumClause
canonicalYMSpectralContinuumClauses =
  spectralMarginRouteImported
  ∷ h3aPrincipalIntakeSocketImported
  ∷ h3bDownstreamSocketImported
  ∷ finiteVolumeToBulkGapRecorded
  ∷ rgResidualHonestyRetained
  ∷ noSpectralPollutionDependsOnH3aH3b
  ∷ osWightmanSocketRecorded
  ∷ []

ymSpectralContinuumClauseCount : Nat
ymSpectralContinuumClauseCount = listLength canonicalYMSpectralContinuumClauses

ymSpectralContinuumClauseCountIs7 : ymSpectralContinuumClauseCount ≡ 7
ymSpectralContinuumClauseCountIs7 = refl

data YMSpectralContinuumBlocker : Set where
  blocker-h3aPrincipalIntakeStillOpen : YMSpectralContinuumBlocker
  blocker-h3bDownstreamStillOpen : YMSpectralContinuumBlocker
  blocker-nospectralpollutionStillOpen : YMSpectralContinuumBlocker
  blocker-osWightmanStillOpen : YMSpectralContinuumBlocker
  blocker-ymClayPromotionForbidden : YMSpectralContinuumBlocker

canonicalYMSpectralContinuumBlockers : List YMSpectralContinuumBlocker
canonicalYMSpectralContinuumBlockers =
  blocker-h3aPrincipalIntakeStillOpen
  ∷ blocker-h3bDownstreamStillOpen
  ∷ blocker-nospectralpollutionStillOpen
  ∷ blocker-osWightmanStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMSpectralMarginToContinuumTransferCompositeRecorded : Bool
YMSpectralMarginToContinuumTransferCompositeRecorded = true

YMSpectralMarginToContinuumTransferCompositeProved : Bool
YMSpectralMarginToContinuumTransferCompositeProved = false

record YMSpectralMarginToContinuumTransferCompositeLightweightBoundary : Set where
  field
    clauses : List YMSpectralContinuumClause
    clausesCanonical : clauses ≡ canonicalYMSpectralContinuumClauses
    blockers : List YMSpectralContinuumBlocker
    blockersCanonical : blockers ≡ canonicalYMSpectralContinuumBlockers
    clauseCountIs7 : ymSpectralContinuumClauseCount ≡ 7
    spectralMarginFeedsH3a : Bool
    spectralMarginFeedsH3aIsTrue :
      spectralMarginFeedsH3a ≡ true
    h3aFeedsH3b : Bool
    h3aFeedsH3bIsTrue :
      h3aFeedsH3b ≡ true
    noSpectralPollutionWaitsForH3aH3b : Bool
    noSpectralPollutionWaitsForH3aH3bIsTrue :
      noSpectralPollutionWaitsForH3aH3b ≡ true
    provedStillFalse :
      YMSpectralMarginToContinuumTransferCompositeProved ≡ false
    failClosedBoundary : List YMSpectralContinuumClause

canonicalYMSpectralMarginToContinuumTransferCompositeLightweightBoundary :
  YMSpectralMarginToContinuumTransferCompositeLightweightBoundary
canonicalYMSpectralMarginToContinuumTransferCompositeLightweightBoundary =
  record
    { clauses = canonicalYMSpectralContinuumClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMSpectralContinuumBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; spectralMarginFeedsH3a = true
    ; spectralMarginFeedsH3aIsTrue = refl
    ; h3aFeedsH3b = true
    ; h3aFeedsH3bIsTrue = refl
    ; noSpectralPollutionWaitsForH3aH3b = true
    ; noSpectralPollutionWaitsForH3aH3bIsTrue = refl
    ; provedStillFalse = refl
    ; failClosedBoundary =
        spectralMarginRouteImported
        ∷ h3aPrincipalIntakeSocketImported
        ∷ h3bDownstreamSocketImported
        ∷ noSpectralPollutionDependsOnH3aH3b
        ∷ []
    }

YMSpectralMarginToContinuumTransferCompositeRecordedIsTrue :
  YMSpectralMarginToContinuumTransferCompositeRecorded ≡ true
YMSpectralMarginToContinuumTransferCompositeRecordedIsTrue = refl
