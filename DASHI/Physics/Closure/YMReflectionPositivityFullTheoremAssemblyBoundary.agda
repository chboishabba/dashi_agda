module DASHI.Physics.Closure.YMReflectionPositivityFullTheoremAssemblyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

balabanBurdenRouteClause : String
balabanBurdenRouteClause =
  "Reflection positivity consumes the Balaban H3a.3/H3a.4/H3a.5 intake downstream; it does not create a separate external mathematical burden."

data YMReflectionPositivityAssemblyClause : Set where
  tauThetaCommutativityImported : YMReflectionPositivityAssemblyClause
  actionSplitImported : YMReflectionPositivityAssemblyClause
  transferMatrixHermitianImported : YMReflectionPositivityAssemblyClause
  osAxiomImported : YMReflectionPositivityAssemblyClause
  citedAuthorityBalabanH3aClusterNotClosedHere :
    YMReflectionPositivityAssemblyClause
  rpOsRouteRecordedAsCitedConsumer :
    YMReflectionPositivityAssemblyClause
  osWightmanRouteStillDownstreamConsumerOfH3aAndH3b :
    YMReflectionPositivityAssemblyClause
  clayPromotionStillBlocked : YMReflectionPositivityAssemblyClause

canonicalYMReflectionPositivityAssemblyClauses :
  List YMReflectionPositivityAssemblyClause
canonicalYMReflectionPositivityAssemblyClauses =
  tauThetaCommutativityImported
  ∷ actionSplitImported
  ∷ transferMatrixHermitianImported
  ∷ osAxiomImported
  ∷ citedAuthorityBalabanH3aClusterNotClosedHere
  ∷ rpOsRouteRecordedAsCitedConsumer
  ∷ osWightmanRouteStillDownstreamConsumerOfH3aAndH3b
  ∷ clayPromotionStillBlocked
  ∷ []

ymReflectionPositivityAssemblyClauseCount : Nat
ymReflectionPositivityAssemblyClauseCount =
  listLength canonicalYMReflectionPositivityAssemblyClauses

ymReflectionPositivityAssemblyClauseCountIs8 :
  ymReflectionPositivityAssemblyClauseCount ≡ 8
ymReflectionPositivityAssemblyClauseCountIs8 = refl

data YMReflectionPositivityConsumer : Set where
  consumer-rp-os :
    YMReflectionPositivityConsumer
  consumer-wightman :
    YMReflectionPositivityConsumer
  consumer-final-mass-gap-transfer :
    YMReflectionPositivityConsumer

canonicalYMReflectionPositivityConsumers :
  List YMReflectionPositivityConsumer
canonicalYMReflectionPositivityConsumers =
  consumer-rp-os
  ∷ consumer-wightman
  ∷ consumer-final-mass-gap-transfer
  ∷ []

ymReflectionPositivityConsumerCount : Nat
ymReflectionPositivityConsumerCount =
  listLength canonicalYMReflectionPositivityConsumers

ymReflectionPositivityConsumerCountIs3 :
  ymReflectionPositivityConsumerCount ≡ 3
ymReflectionPositivityConsumerCountIs3 = refl

data YMReflectionPositivityAssemblyBlocker : Set where
  blocker-balabanH3a3FiniteVolumeMassGapStillExternal :
    YMReflectionPositivityAssemblyBlocker
  blocker-balabanH3a4InfiniteVolumeControlStillExternal :
    YMReflectionPositivityAssemblyBlocker
  blocker-balabanH3a5ContinuumTransferStillExternal :
    YMReflectionPositivityAssemblyBlocker
  blocker-ymClayPromotionForbidden : YMReflectionPositivityAssemblyBlocker

canonicalYMReflectionPositivityAssemblyBlockers :
  List YMReflectionPositivityAssemblyBlocker
canonicalYMReflectionPositivityAssemblyBlockers =
  blocker-balabanH3a3FiniteVolumeMassGapStillExternal
  ∷ blocker-balabanH3a4InfiniteVolumeControlStillExternal
  ∷ blocker-balabanH3a5ContinuumTransferStillExternal
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

ymReflectionPositivityAssemblyBlockerCount : Nat
ymReflectionPositivityAssemblyBlockerCount =
  listLength canonicalYMReflectionPositivityAssemblyBlockers

ymReflectionPositivityAssemblyBlockerCountIs4 :
  ymReflectionPositivityAssemblyBlockerCount ≡ 4
ymReflectionPositivityAssemblyBlockerCountIs4 = refl

YMReflectionPositivityFullTheoremAssemblyRecorded : Bool
YMReflectionPositivityFullTheoremAssemblyRecorded = true

YMReflectionPositivityFullTheoremAssemblyProved : Bool
YMReflectionPositivityFullTheoremAssemblyProved = false

YMReflectionPositivityFullTheoremAssemblyAuthorityAudited : Bool
YMReflectionPositivityFullTheoremAssemblyAuthorityAudited = false

YMReflectionPositivityFullTheoremAssemblySubmissionReady : Bool
YMReflectionPositivityFullTheoremAssemblySubmissionReady = false

record YMReflectionPositivityFullTheoremAssemblyBoundary : Set where
  field
    clauses : List YMReflectionPositivityAssemblyClause
    clausesCanonical : clauses ≡ canonicalYMReflectionPositivityAssemblyClauses
    citedConsumers :
      List YMReflectionPositivityConsumer
    citedConsumersCanonical :
      citedConsumers ≡ canonicalYMReflectionPositivityConsumers
    blockers : List YMReflectionPositivityAssemblyBlocker
    blockersCanonical : blockers ≡ canonicalYMReflectionPositivityAssemblyBlockers
    clauseCountIs8 : ymReflectionPositivityAssemblyClauseCount ≡ 8
    consumerCountIs3 :
      ymReflectionPositivityConsumerCount ≡ 3
    blockerCountIs4 :
      ymReflectionPositivityAssemblyBlockerCount ≡ 4
    balabanRouteClause : String
    authorityAuditStillFalse :
      YMReflectionPositivityFullTheoremAssemblyAuthorityAudited ≡ false
    submissionReadyStillFalse :
      YMReflectionPositivityFullTheoremAssemblySubmissionReady ≡ false
    theoremStillFalse : YMReflectionPositivityFullTheoremAssemblyProved ≡ false

canonicalYMReflectionPositivityFullTheoremAssemblyBoundary :
  YMReflectionPositivityFullTheoremAssemblyBoundary
canonicalYMReflectionPositivityFullTheoremAssemblyBoundary =
  record
    { clauses = canonicalYMReflectionPositivityAssemblyClauses
    ; clausesCanonical = refl
    ; citedConsumers = canonicalYMReflectionPositivityConsumers
    ; citedConsumersCanonical = refl
    ; blockers = canonicalYMReflectionPositivityAssemblyBlockers
    ; blockersCanonical = refl
    ; clauseCountIs8 = refl
    ; consumerCountIs3 = refl
    ; blockerCountIs4 = refl
    ; balabanRouteClause = balabanBurdenRouteClause
    ; authorityAuditStillFalse = refl
    ; submissionReadyStillFalse = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivityFullTheoremAssemblyRecordedIsTrue :
  YMReflectionPositivityFullTheoremAssemblyRecorded ≡ true
YMReflectionPositivityFullTheoremAssemblyRecordedIsTrue = refl
