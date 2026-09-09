module DASHI.Physics.ExoticGravity.AntigravitySharedSourceProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Physics.ExoticGravity.AntigravityProofSearchFrontierExact as Frontier
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentSearchHypergraphExact as Hyper
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Enhancement

------------------------------------------------------------------------
-- SHARED-SOURCE MULTI-CONSUMER CUT
--
-- Five live consumers currently ask for source/apparatus information.  This
-- owner permits one physical acquisition to pay several leaves only when one
-- same-apparatus receipt carries the exact per-consumer post-state witnesses.
------------------------------------------------------------------------

data SharedSourceConsumer : Set where
  evidenceSourceCharacterisation : SharedSourceConsumer
  couplingSourceObservable : SharedSourceConsumer
  grComparatorGeometry : SharedSourceConsumer
  literalGeometrySourceShape : SharedSourceConsumer
  enhancementSourceCurrentAndStressEnergy : SharedSourceConsumer

currentEnhancementLeafIsSourceCurrent :
  Enhancement.currentFirstOpenEnhancementLeaf ≡ Enhancement.sourceCurrentLeaf
currentEnhancementLeafIsSourceCurrent = refl

sharedSourceCandidateMove : Choice.InformationMove
sharedSourceCandidateMove = Hyper.characteriseSourceMove

------------------------------------------------------------------------
-- Enhancement payment is explicitly stronger than merely naming the source
-- current leaf: the existing candidate move says it measures/reconstructs both
-- mass-current and stress-energy, so a multi-payment receipt must prove both.
------------------------------------------------------------------------

record EnhancementSourcePayment : Set where
  constructor enhancement-source-payment
  field
    apparatusCarrier : String
    state : Enhancement.EnhancementClosureState
    sourceCurrentPaid : Enhancement.sourceCurrentOwned state ≡ true
    sourceStressEnergyPaid : Enhancement.sourceStressEnergyOwned state ≡ true

open EnhancementSourcePayment public

record SharedSourceCutPayment : Set where
  constructor shared-source-cut-payment
  field
    basePayment : Frontier.SharedSourceAcquisitionReceipt
    enhancementPayment : EnhancementSourcePayment
    commonApparatusCarrier : String
    baseCarrierMatches :
      Frontier.apparatusCarrier basePayment ≡ commonApparatusCarrier
    enhancementCarrierMatches :
      EnhancementSourcePayment.apparatusCarrier enhancementPayment
        ≡ commonApparatusCarrier

open SharedSourceCutPayment public

------------------------------------------------------------------------
-- No canonical payment is constructed.  A protocol description is a candidate
-- move, not evidence that the measurements were actually acquired on one
-- apparatus and accepted by every consumer.
------------------------------------------------------------------------

data SharedSourcePaymentAuthority : Set where

candidateSharedMoveDoesNotCreatePayment :
  SharedSourcePaymentAuthority → ⊥
candidateSharedMoveDoesNotCreatePayment ()

------------------------------------------------------------------------
-- If a real shared payment does include both enhancement source coordinates,
-- the enhancement frontier advances to geometry rather than charging source
-- current and stress-energy as two separate future experiments.
------------------------------------------------------------------------

postSharedEnhancementState : Enhancement.EnhancementClosureState
postSharedEnhancementState =
  Enhancement.enhancement-closure-state true true false false false false

postSharedEnhancementFirstOpen :
  Enhancement.firstOpenEnhancementLeaf postSharedEnhancementState
    ≡ Enhancement.geometryLeaf
postSharedEnhancementFirstOpen = refl

record SharedSourceProofSearchBoundary : Set where
  constructor shared-source-proof-search-boundary
  field
    multipleConsumersCurrentlyNeedSourceInformation : Bool
    sameWordsAutomaticallyMeanSameCarrier : Bool
    oneAcquisitionMayPayMultipleConsumersWithExactReceipt : Bool
    sharedPaymentMustBindOneApparatusCarrier : Bool
    enhancementPaymentMustIncludeCurrentAndStressEnergy : Bool
    candidateMoveAutomaticallyCreatesSharedPayment : Bool
    successfulSharedPaymentMaySkipDuplicateSourceAcquisitions : Bool
    sharedPaymentAutomaticallyProvesConstitutiveEnhancement : Bool
    sharedPaymentAutomaticallyProvesAntigravity : Bool

canonicalSharedSourceProofSearchBoundary : SharedSourceProofSearchBoundary
canonicalSharedSourceProofSearchBoundary =
  shared-source-proof-search-boundary
    true false true true true false true false false
