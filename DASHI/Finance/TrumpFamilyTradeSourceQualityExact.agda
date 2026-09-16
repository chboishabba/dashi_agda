module DASHI.Finance.TrumpFamilyTradeSourceQualityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- CLAIM-LEVEL EVIDENCE QUALITY
--
-- Quality is proposition-relative.  A primary filing may strongly support an
-- ownership quantity while saying nothing about motive, causal policy effect,
-- hidden information, or legality.  Independent corroboration is therefore a
-- separate axis rather than a scalar replacement for proposition matching.
------------------------------------------------------------------------

record ClaimEvidenceQuality (claim : Atlas.TradeEvidenceClaim) : Set where
  constructor claim-evidence-quality
  field
    exactDocumentIdentityPaid : Bool
    exactEntityIdentityPaid : Bool
    exactEventTimePaid : Bool
    propositionScopePaid : Bool
    primaryDocumentPaid : Bool
    independentCorroborationPaid : Bool
    counterevidenceSearchPaid : Bool
    legalStatusPaid : Bool
    motivePaid : Bool

open ClaimEvidenceQuality public

record PromotionReadyFor
    (claim : Atlas.TradeEvidenceClaim)
    (quality : ClaimEvidenceQuality claim) : Set where
  constructor promotion-ready-for
  field
    requiredDocumentIdentity : exactDocumentIdentityPaid quality ≡ true
    requiredEntityIdentity : exactEntityIdentityPaid quality ≡ true
    requiredEventTime : exactEventTimePaid quality ≡ true
    requiredPropositionScope : propositionScopePaid quality ≡ true

open PromotionReadyFor public

------------------------------------------------------------------------
-- Concrete current states.  These do not pretend every axis must be paid for
-- every consumer: legal/motive/counterevidence axes remain unpaid unless the
-- downstream question actually requires them.
------------------------------------------------------------------------

donJrDominariQuality : ClaimEvidenceQuality Atlas.donJrDominariWarrantExercise
donJrDominariQuality =
  claim-evidence-quality true true true true true false false false false

ericABTCQuality : ClaimEvidenceQuality Atlas.ericAmericanBitcoinOwnership
ericABTCQuality =
  claim-evidence-quality true true true true true false false false false

trumpTMTGTrustQuality : ClaimEvidenceQuality Atlas.trumpTMTGTrustDisclosure
trumpTMTGTrustQuality =
  claim-evidence-quality true true true true true false false false false

trumpLate278TQuality : ClaimEvidenceQuality Atlas.trumpLateTransactionReportingFees
trumpLate278TQuality =
  claim-evidence-quality true true true true true false false false false

truthAPIQuality : ClaimEvidenceQuality Atlas.truthAPIPrimary
truthAPIQuality =
  claim-evidence-quality true true true true true false false false false

truthAPIConcernQuality : ClaimEvidenceQuality Atlas.truthAPIRegulatoryConcern
truthAPIConcernQuality =
  claim-evidence-quality true true true true true false false false false

------------------------------------------------------------------------
-- Non-promotion laws.
------------------------------------------------------------------------

data PrimarySourceAutomaticallyPaysMotive : Set where
data CorroborationAutomaticallyPaysLegalStatus : Set where
data ExactTimingAutomaticallyPaysCausation : Set where
data OwnershipEvidenceAutomaticallyPaysControl : Set where

primaryDoesNotPayMotive : PrimarySourceAutomaticallyPaysMotive → ⊥
primaryDoesNotPayMotive ()

corroborationDoesNotPayLegalStatus : CorroborationAutomaticallyPaysLegalStatus → ⊥
corroborationDoesNotPayLegalStatus ()

timingDoesNotPayCausation : ExactTimingAutomaticallyPaysCausation → ⊥
timingDoesNotPayCausation ()

ownershipDoesNotPayControl : OwnershipEvidenceAutomaticallyPaysControl → ⊥
ownershipDoesNotPayControl ()

record SourceQualityBoundary : Set where
  constructor source-quality-boundary
  field
    qualityIsClaimRelative : Bool
    primaryAndIndependentAreSeparateAxes : Bool
    timingAndCausationAreSeparateAxes : Bool
    ownershipAndControlAreSeparateAxes : Bool
    motiveRequiresIndependentPayment : Bool

canonicalSourceQualityBoundary : SourceQualityBoundary
canonicalSourceQualityBoundary =
  source-quality-boundary true true true true true
