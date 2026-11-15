module DASHI.Cognition.CCDCOEP3EvidenceStageIdentificationExact where

------------------------------------------------------------------------
-- P3 CAUSAL EVIDENCE LADDER: NO AUTOMATIC PROMOTION BETWEEN
-- draft, institutional approval, funding, executed activity and effect.
--
-- The 3 April 1998 plan reproduced in Congressional Record H2325-H2327
-- states that initiatives are launched AFTER plan approval, funding,
-- and resource arrangement (source text lines 659-664).
--
-- These finite models are deliberate logical counterexamples, NOT
-- five observed historical worlds or an attribution of actual spending.
-- The existing NonFactorability and DiscriminatorSynthesis owners
-- provide all mathematical factorisation and positive-probe machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as D
import DASHI.Cognition.CCDCOEP3API1998PrimaryPlanExact as Plan

data CaseWorld : Set where
  draftWithoutApproval : CaseWorld
  approvedWithoutFunding : CaseWorld
  fundedWithoutDelivery : CaseWorld
  deliveredWithoutEstablishedEffect : CaseWorld
  deliveredWithEstablishedEffect : CaseWorld

-- These are five distinct QUERIES; a common Boolean result type does
-- not identify their original evidence sources or causal meaning.
draftKnown : CaseWorld → Bool
draftKnown _ = true

approvalKnown : CaseWorld → Bool
approvalKnown draftWithoutApproval = false
approvalKnown _ = true

fundingKnown : CaseWorld → Bool
fundingKnown draftWithoutApproval = false
fundingKnown approvedWithoutFunding = false
fundingKnown _ = true

deliveryKnown : CaseWorld → Bool
deliveryKnown draftWithoutApproval = false
deliveryKnown approvedWithoutFunding = false
deliveryKnown fundedWithoutDelivery = false
deliveryKnown _ = true

effectEstablished : CaseWorld → Bool
effectEstablished deliveredWithEstablishedEffect = true
effectEstablished _ = false

-- A *published draft* alone cannot identify authorisation.
draftDoesNotDetermineApproval :
  NF.FactorsThrough draftKnown approvalKnown → ⊥
draftDoesNotDetermineApproval =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      draftWithoutApproval approvedWithoutFunding refl (λ ()))

-- Even proof of company adoption would not identify actual funding.
approvalDoesNotDetermineFunding :
  NF.FactorsThrough approvalKnown fundingKnown → ⊥
approvalDoesNotDetermineFunding =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      approvedWithoutFunding fundedWithoutDelivery refl (λ ()))

-- Real payment is still not a verified distribution/exposure event.
fundingDoesNotDetermineDelivery :
  NF.FactorsThrough fundingKnown deliveryKnown → ⊥
fundingDoesNotDetermineDelivery =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      fundedWithoutDelivery deliveredWithoutEstablishedEffect refl (λ ()))

-- Even actually delivered advocacy does not identify audience or
-- policy effect without a comparison design and measured observations.
deliveryDoesNotDetermineEffect :
  NF.FactorsThrough deliveryKnown effectEstablished → ⊥
deliveryDoesNotDetermineEffect =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      deliveredWithoutEstablishedEffect deliveredWithEstablishedEffect
      refl (λ ()))

approvalSourceProbe : D.ExperimentBundle CaseWorld
approvalSourceProbe =
  D.experimentBundle
    Bool approvalKnown 1
    "Check signed organisational approval adopting the specific 1998 plan"
    "Hypothetical external document query; no original approval admitted"

fundingSourceProbe : D.ExperimentBundle CaseWorld
fundingSourceProbe =
  D.experimentBundle
    Bool fundingKnown 1
    "Check approved invoices/disbursements, dates and payers for that plan"
    "Hypothetical original financial-source query; no payment admitted"

deliverySourceProbe : D.ExperimentBundle CaseWorld
deliverySourceProbe =
  D.experimentBundle
    Bool deliveryKnown 1
    "Check dated communications actually delivered under the specific plan"
    "Hypothetical delivery/exposure query; no executed receipt admitted"

effectSourceProbe : D.ExperimentBundle CaseWorld
effectSourceProbe =
  D.experimentBundle
    Bool effectEstablished 1
    "Compare independently measured outcomes under a justified design"
    "Hypothetical causal-contrast oracle, not a real identified effect"

approvalProbeSeparates :
  D.BundleSeparates approvalSourceProbe
    draftWithoutApproval approvedWithoutFunding
approvalProbeSeparates = D.bundleSeparates (λ ())

fundingProbeSeparates :
  D.BundleSeparates fundingSourceProbe
    approvedWithoutFunding fundedWithoutDelivery
fundingProbeSeparates = D.bundleSeparates (λ ())

deliveryProbeSeparates :
  D.BundleSeparates deliverySourceProbe
    fundedWithoutDelivery deliveredWithoutEstablishedEffect
deliveryProbeSeparates = D.bundleSeparates (λ ())

effectProbeSeparates :
  D.BundleSeparates effectSourceProbe
    deliveredWithoutEstablishedEffect deliveredWithEstablishedEffect
effectProbeSeparates = D.bundleSeparates (λ ())

-- The historical 1998 primary document is the actual upstream anchor.
-- Its own epistemic status remains "draft", not realised intervention.
publishedPrimaryIsDraft :
  Plan.publicDraftObservation Plan.unimplementedWorld
  ≡ Plan.draftRecorded
publishedPrimaryIsDraft = refl

-- Each positive separator describes which ORIGINAL kind of evidence
-- would make progress. None inhabits an empirical measured-world
-- acceptance type. The causal estimand, interference, uncertainty,
-- missingness and confounding remain source-specific obligations.
