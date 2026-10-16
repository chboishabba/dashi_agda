module DASHI.Biology.AutismVaccineAttributionRuleConformanceExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.AutismVaccineExternalSourceAtlasExact as Atlas
import DASHI.Biology.AttributionConsumerNonDescentExact as Consumer
import DASHI.Biology.AutismVaccineClaimPromotionAuditExact as Audit
import DASHI.Biology.AutismVaccineStrictBindingInstantiationExact as StrictBinding

------------------------------------------------------------------------
-- AUTISM/VACCINE ATTRIBUTION-RULE CONFORMANCE
--
-- This owner makes the repo-wide attribution firewalls explicit for the
-- Hbomberguy / Wakefield / Deer / external-science / DASHI-synthesis lane.
-- Existing owners already provide the claim-relative source objects and typed
-- evidence->claim->estimand bindings. This module adds the later generic
-- provenance/priority/unknown-coordinate firewalls so the older lane cannot be
-- read more strongly than the rest of DASHI.
------------------------------------------------------------------------

data ScientificSupportProvesPriorityPermission : Set where
data PriorityProvesCorrectnessPermission : Set where
data ContactOrExposureProvesDerivationPermission : Set where
data ContactOrExposureProvesPlagiarismPermission : Set where
data UnknownCoordinateEqualsZeroPermission : Set where
data UnpaidCoordinateEqualsZeroPermission : Set where
data ExternalSourceOwnsDASHISynthesisPermission : Set where

scientificSupportDoesNotProvePriority : ScientificSupportProvesPriorityPermission → ⊥
scientificSupportDoesNotProvePriority ()

priorityDoesNotProveCorrectness : PriorityProvesCorrectnessPermission → ⊥
priorityDoesNotProveCorrectness ()

contactOrExposureDoesNotProveDerivation : ContactOrExposureProvesDerivationPermission → ⊥
contactOrExposureDoesNotProveDerivation ()

contactOrExposureDoesNotProvePlagiarism : ContactOrExposureProvesPlagiarismPermission → ⊥
contactOrExposureDoesNotProvePlagiarism ()

unknownCoordinateDoesNotEqualZero : UnknownCoordinateEqualsZeroPermission → ⊥
unknownCoordinateDoesNotEqualZero ()

unpaidCoordinateDoesNotEqualZero : UnpaidCoordinateEqualsZeroPermission → ⊥
unpaidCoordinateDoesNotEqualZero ()

externalSourceDoesNotOwnDASHISynthesis : ExternalSourceOwnsDASHISynthesisPermission → ⊥
externalSourceDoesNotOwnDASHISynthesis ()

record AutismVaccineAttributionRuleBoundary : Set where
  constructor autism-vaccine-attribution-rule-boundary
  field
    sourceAtlas : Source.AttributedSourceAtlas
    sourceAtlasIsCanonical : sourceAtlas ≡ Atlas.canonicalAutismVaccineSourceAtlas
    sourceAtlasCreatesAuthority : Bool
    sourceAtlasCreatesAuthorityIsFalse : sourceAtlasCreatesAuthority ≡ false
    citationCreatesProof : Bool
    citationCreatesProofIsFalse : citationCreatesProof ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false
    sourceIdentityDeterminesEndpointMeaning : Bool
    sourceIdentityDeterminesEndpointMeaningIsFalse : sourceIdentityDeterminesEndpointMeaning ≡ false
    sourceIdentityImportsTruthOrCausalAuthority : Bool
    sourceIdentityImportsTruthOrCausalAuthorityIsFalse : sourceIdentityImportsTruthOrCausalAuthority ≡ false
    scientificSupportProvesPriority : Bool
    scientificSupportProvesPriorityIsFalse : scientificSupportProvesPriority ≡ false
    priorityProvesCorrectness : Bool
    priorityProvesCorrectnessIsFalse : priorityProvesCorrectness ≡ false
    contactOrExposureProvesDerivation : Bool
    contactOrExposureProvesDerivationIsFalse : contactOrExposureProvesDerivation ≡ false
    contactOrExposureProvesPlagiarism : Bool
    contactOrExposureProvesPlagiarismIsFalse : contactOrExposureProvesPlagiarism ≡ false
    unknownCoordinateEqualsZero : Bool
    unknownCoordinateEqualsZeroIsFalse : unknownCoordinateEqualsZero ≡ false
    unpaidCoordinateEqualsZero : Bool
    unpaidCoordinateEqualsZeroIsFalse : unpaidCoordinateEqualsZero ≡ false
    externalSourceOwnsDASHISynthesis : Bool
    externalSourceOwnsDASHISynthesisIsFalse : externalSourceOwnsDASHISynthesis ≡ false
    strictSameObjectSameEstimandBindingPresent : Bool
    strictSameObjectSameEstimandBindingPresentIsTrue : strictSameObjectSameEstimandBindingPresent ≡ true
    reading : String

open AutismVaccineAttributionRuleBoundary public

canonicalAutismVaccineAttributionRuleBoundary : AutismVaccineAttributionRuleBoundary
canonicalAutismVaccineAttributionRuleBoundary =
  autism-vaccine-attribution-rule-boundary
    Atlas.canonicalAutismVaccineSourceAtlas
    refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "Hbomberguy, Wakefield, Brian Deer/independent investigative records, quoted speakers, external scientific sources and DASHI synthesis retain distinct ownership. Citation records provenance but imports neither proof nor authority. Scientific support does not establish priority; priority does not establish correctness; contact/exposure does not establish derivation or plagiarism; unknown/unpaid coordinates are not zero; and evidentiary promotion must use typed exact evidence-to-claim and evidence-to-estimand witnesses."

canonicalSourceAtlasAuthorityReceipt :
  Source.atlasCreatesAuthority (sourceAtlas canonicalAutismVaccineAttributionRuleBoundary) ≡ false
canonicalSourceAtlasAuthorityReceipt = Atlas.canonicalAtlasDoesNotCreateAuthority

canonicalSourceConsumerTruthReceipt :
  Consumer.sourceIdentityImportsTruthAuthority Consumer.canonicalAttributionConsumerBoundary ≡ false
canonicalSourceConsumerTruthReceipt = refl

canonicalSourceConsumerCausalReceipt :
  Consumer.sourceIdentityImportsCausalAuthority Consumer.canonicalAttributionConsumerBoundary ≡ false
canonicalSourceConsumerCausalReceipt = refl

canonicalSourceConsumerSynthesisReceipt :
  Consumer.dashiSynthesisBackAttributedToSource Consumer.canonicalAttributionConsumerBoundary ≡ false
canonicalSourceConsumerSynthesisReceipt = refl

canonicalHviidEvidenceClaimWitness :
  StrictBinding.EvidencePaysClaim Audit.hviid2019Receipt Audit.hbombMMRNoLinkClaim
canonicalHviidEvidenceClaimWitness =
  StrictBinding.hviidPaysNoLink

canonicalHviidEstimandWitness :
  StrictBinding.EvidenceMatchesEstimand
    Audit.hviid2019Receipt
    StrictBinding.mmrAutismPopulationEstimand
canonicalHviidEstimandWitness =
  StrictBinding.hviidMatchesPopulationEstimand
