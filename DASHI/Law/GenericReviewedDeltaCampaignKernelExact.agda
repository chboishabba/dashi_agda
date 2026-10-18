module DASHI.Law.GenericReviewedDeltaCampaignKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)

------------------------------------------------------------------------
-- Pure generic campaign kernel.
--
-- The reusable recursion is only:
--   recompute residuals -> select fresh demand -> accept REVIEWED delta
--   -> apply -> recompute.
--
-- Acquisition, review, domain semantics and authority admission stay outside.
------------------------------------------------------------------------

data DemoWorld : Set where
  nonePaid : DemoWorld
  firstPaid : DemoWorld
  allPaid : DemoWorld

data DemoResidual : Set where
  firstResidual secondResidual : DemoResidual

data DemoDemand : Set where
  firstDemand secondDemand : DemoDemand

data ReviewedDelta : Set where
  payFirst paySecond : ReviewedDelta

recompute : DemoWorld → List DemoResidual
recompute nonePaid = firstResidual ∷ secondResidual ∷ []
recompute firstPaid = secondResidual ∷ []
recompute allPaid = []

selectFresh : List DemoResidual → Maybe DemoDemand
selectFresh [] = nothing
selectFresh (firstResidual ∷ rest) = just firstDemand
selectFresh (secondResidual ∷ rest) = just secondDemand

applyReviewed : DemoWorld → ReviewedDelta → DemoWorld
applyReviewed nonePaid payFirst = firstPaid
applyReviewed firstPaid paySecond = allPaid
applyReviewed nonePaid paySecond = nonePaid
applyReviewed firstPaid payFirst = firstPaid
applyReviewed allPaid delta = allPaid

firstReviewedDeltaRecomputes :
  recompute (applyReviewed nonePaid payFirst)
  ≡
  secondResidual ∷ []
firstReviewedDeltaRecomputes = refl

secondReviewedDeltaCloses :
  recompute (applyReviewed firstPaid paySecond) ≡ []
secondReviewedDeltaCloses = refl

record GenericReviewedDeltaCampaignKernelBoundary : Set where
  constructor genericReviewedDeltaCampaignKernelBoundary
  field
    kernelOwnsResidualRecomputation : Bool
    kernelOwnsResidualRecomputationIsTrue :
      kernelOwnsResidualRecomputation ≡ true

    kernelMaySelectFreshDemand : Bool
    kernelMaySelectFreshDemandIsTrue :
      kernelMaySelectFreshDemand ≡ true

    kernelAcceptsOnlyReviewedDeltaInterface : Bool
    kernelAcceptsOnlyReviewedDeltaInterfaceIsTrue :
      kernelAcceptsOnlyReviewedDeltaInterface ≡ true

    kernelMayConvertRawSourceIntoReviewedDelta : Bool
    kernelMayConvertRawSourceIntoReviewedDeltaIsFalse :
      kernelMayConvertRawSourceIntoReviewedDelta ≡ false

    kernelMayBypassDomainReview : Bool
    kernelMayBypassDomainReviewIsFalse :
      kernelMayBypassDomainReview ≡ false

    kernelRequiresContractDoctrine : Bool
    kernelRequiresContractDoctrineIsFalse :
      kernelRequiresContractDoctrine ≡ false

    kernelCreatesLegalAuthority : Bool
    kernelCreatesLegalAuthorityIsFalse :
      kernelCreatesLegalAuthority ≡ false

    kernelCreatesClaimTruth : Bool
    kernelCreatesClaimTruthIsFalse :
      kernelCreatesClaimTruth ≡ false

open GenericReviewedDeltaCampaignKernelBoundary public

canonicalGenericReviewedDeltaCampaignKernelBoundary :
  GenericReviewedDeltaCampaignKernelBoundary
canonicalGenericReviewedDeltaCampaignKernelBoundary =
  genericReviewedDeltaCampaignKernelBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

data RawSourceAutomaticallyReviewedDelta : Set where
data KernelAutomaticallyContractSpecific : Set where
data KernelAutomaticallyAuthority : Set where

rawSourceDoesNotBecomeReviewedDelta :
  RawSourceAutomaticallyReviewedDelta → ⊥
rawSourceDoesNotBecomeReviewedDelta ()

kernelIsNotAutomaticallyContractSpecific :
  KernelAutomaticallyContractSpecific → ⊥
kernelIsNotAutomaticallyContractSpecific ()

kernelDoesNotCreateAuthority :
  KernelAutomaticallyAuthority → ⊥
kernelDoesNotCreateAuthority ()