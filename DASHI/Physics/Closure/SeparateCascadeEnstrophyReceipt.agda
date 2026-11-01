module DASHI.Physics.Closure.SeparateCascadeEnstrophyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Option 3: separate cascade/enstrophy diagnostic receipt.

data CascadeBase : Set where
  p2 : CascadeBase
  p3 : CascadeBase
  p5 : CascadeBase

canonicalCascadeBases : List CascadeBase
canonicalCascadeBases =
  p2 ∷ p3 ∷ p5 ∷ []

data SeparateCascadeChain : Set where
  cascadeChainP2 : SeparateCascadeChain
  cascadeChainP3 : SeparateCascadeChain
  cascadeChainP5 : SeparateCascadeChain

canonicalSeparateCascadeChains :
  List SeparateCascadeChain
canonicalSeparateCascadeChains =
  cascadeChainP2
  ∷ cascadeChainP3
  ∷ cascadeChainP5
  ∷ []

data SeparateEnstrophy : Set where
  E2 : SeparateEnstrophy
  E3 : SeparateEnstrophy
  E5 : SeparateEnstrophy

canonicalSeparateEnstrophies :
  List SeparateEnstrophy
canonicalSeparateEnstrophies =
  E2 ∷ E3 ∷ E5 ∷ []

data InterBaseTransferStatus : Set where
  exactInterBaseTransferVanishingWouldBeValuable :
    InterBaseTransferStatus

  projectedApproximateVanishingDiagnosticOnly :
    InterBaseTransferStatus

  exactIndependentConservationLawNotProven :
    InterBaseTransferStatus

canonicalInterBaseTransferStatus :
  List InterBaseTransferStatus
canonicalInterBaseTransferStatus =
  exactInterBaseTransferVanishingWouldBeValuable
  ∷ projectedApproximateVanishingDiagnosticOnly
  ∷ exactIndependentConservationLawNotProven
  ∷ []

separateCascadeEnstrophyStatement : String
separateCascadeEnstrophyStatement =
  "Option 3 records separate p=2,3,5 cascade chains and enstrophies E_p; projected or approximate cross-base transfer killing is diagnostic, while exact inter-base transfer vanishing and an independent conservation law are not proved."

record SeparateCascadeEnstrophyReceipt : Setω where
  field
    cascadeBases :
      List CascadeBase

    cascadeBasesAreCanonical :
      cascadeBases ≡ canonicalCascadeBases

    separateCascadeChains :
      List SeparateCascadeChain

    separateCascadeChainsAreCanonical :
      separateCascadeChains ≡ canonicalSeparateCascadeChains

    separateEnstrophies :
      List SeparateEnstrophy

    separateEnstrophiesAreCanonical :
      separateEnstrophies ≡ canonicalSeparateEnstrophies

    interBaseTransferStatus :
      List InterBaseTransferStatus

    interBaseTransferStatusIsCanonical :
      interBaseTransferStatus ≡ canonicalInterBaseTransferStatus

    separateCascadeChainsRecorded :
      Bool

    separateCascadeChainsRecordedIsTrue :
      separateCascadeChainsRecorded ≡ true

    projectedCrossBaseTransferKilled :
      Bool

    projectedCrossBaseTransferKilledIsTrue :
      projectedCrossBaseTransferKilled ≡ true

    exactInterBaseTransferVanishes :
      Bool

    exactInterBaseTransferVanishesIsFalse :
      exactInterBaseTransferVanishes ≡ false

    newConservationLawConstructed :
      Bool

    newConservationLawConstructedIsFalse :
      newConservationLawConstructed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ separateCascadeEnstrophyStatement

    receiptBoundary :
      List String

open SeparateCascadeEnstrophyReceipt public

canonicalSeparateCascadeEnstrophyReceipt :
  SeparateCascadeEnstrophyReceipt
canonicalSeparateCascadeEnstrophyReceipt =
  record
    { cascadeBases =
        canonicalCascadeBases
    ; cascadeBasesAreCanonical =
        refl
    ; separateCascadeChains =
        canonicalSeparateCascadeChains
    ; separateCascadeChainsAreCanonical =
        refl
    ; separateEnstrophies =
        canonicalSeparateEnstrophies
    ; separateEnstrophiesAreCanonical =
        refl
    ; interBaseTransferStatus =
        canonicalInterBaseTransferStatus
    ; interBaseTransferStatusIsCanonical =
        refl
    ; separateCascadeChainsRecorded =
        true
    ; separateCascadeChainsRecordedIsTrue =
        refl
    ; projectedCrossBaseTransferKilled =
        true
    ; projectedCrossBaseTransferKilledIsTrue =
        refl
    ; exactInterBaseTransferVanishes =
        false
    ; exactInterBaseTransferVanishesIsFalse =
        refl
    ; newConservationLawConstructed =
        false
    ; newConservationLawConstructedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        separateCascadeEnstrophyStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Separate cascade chains are only recorded for p=2,3,5"
        ∷ "Separate enstrophies E_p are recorded as diagnostics"
        ∷ "Inter-base transfer vanishing or smallness would be valuable"
        ∷ "Only projected or approximate cross-base transfer killing is diagnostic here"
        ∷ "No exact independent conservation law is proved"
        ∷ []
    }

separateCascadeChainsRecordedTrue :
  separateCascadeChainsRecorded canonicalSeparateCascadeEnstrophyReceipt
    ≡
    true
separateCascadeChainsRecordedTrue =
  refl

projectedCrossBaseTransferKilledTrue :
  projectedCrossBaseTransferKilled canonicalSeparateCascadeEnstrophyReceipt
    ≡
    true
projectedCrossBaseTransferKilledTrue =
  refl

exactInterBaseTransferVanishesFalse :
  exactInterBaseTransferVanishes canonicalSeparateCascadeEnstrophyReceipt
    ≡
    false
exactInterBaseTransferVanishesFalse =
  refl

newConservationLawConstructedFalse :
  newConservationLawConstructed canonicalSeparateCascadeEnstrophyReceipt
    ≡
    false
newConservationLawConstructedFalse =
  refl

clayNavierStokesPromotedFalse :
  clayNavierStokesPromoted canonicalSeparateCascadeEnstrophyReceipt
    ≡
    false
clayNavierStokesPromotedFalse =
  refl
