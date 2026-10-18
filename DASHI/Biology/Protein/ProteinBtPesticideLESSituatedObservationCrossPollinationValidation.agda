module DASHI.Biology.Protein.ProteinBtPesticideLESSituatedObservationCrossPollinationValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Protein.ProteinBtPesticideLESSituatedObservationCrossPollinationExact as P

boundary = P.canonicalProteinBtPesticideLESBoundary

btIsCompositeObservationProblem :
  P.ProteinBtPesticideLESBoundary.btGenericTokenIsCompleteExposureObject boundary ≡ false
btIsCompositeObservationProblem = refl

assayDependsOnRetainedObjectRole :
  P.ProteinBtPesticideLESBoundary.coarsePesticideTokenDeterminesObserver boundary ≡ false
assayDependsOnRetainedObjectRole = refl

proteinIdentityRemainsQueryRelative :
  P.ProteinBtPesticideLESBoundary.proteinIdentityIsCompletePredictiveState boundary ≡ false
proteinIdentityRemainsQueryRelative = refl

lesContextMustRemainIndependent :
  P.ProteinBtPesticideLESBoundary.pesticideIdentityDeterminesLESDomain boundary ≡ false
lesContextMustRemainIndependent = refl

sourceAttributionDoesNotTransfer :
  P.ProteinBtPesticideLESBoundary.crossPollinationTransfersSourceAuthority boundary ≡ false
sourceAttributionDoesNotTransfer = refl

btProteinDoesNotTransferTRPA1Mechanism :
  P.ProteinBtPesticideLESBoundary.btCryProteinCreatesTRPA1Mechanism boundary ≡ false
btProteinDoesNotTransferTRPA1Mechanism = refl

existingDonorsReused :
  P.ProteinBtPesticideLESBoundary.reusesProteinSituatedHyperfabric boundary ≡ true
existingDonorsReused = refl
