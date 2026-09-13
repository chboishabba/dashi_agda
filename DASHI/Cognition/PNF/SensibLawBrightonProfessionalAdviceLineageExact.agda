module DASHI.Cognition.PNF.SensibLawBrightonProfessionalAdviceLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BRIGHTON PROFESSIONAL TENANCY-ADVICE LINEAGE
--
-- This owner deliberately separates:
--   * matter-originating assertions in Form 11 / Form 16;
--   * notice-process facts in Form 12;
--   * professional tenancy-advice correspondence from QSTARS / Tenants Qld;
--   * any later legal conclusion about breach, retaliation, causation or remedy.
--
-- No private raw email content is embedded here.  The source carriers remain
-- outside the public formalisation; this module records only bounded source
-- roles and the non-promotion boundaries needed by SensibLaw.
------------------------------------------------------------------------

data BrightonAdviceCarrierKind : Set where
  matterForm11Carrier : BrightonAdviceCarrierKind
  matterForm16Carrier : BrightonAdviceCarrierKind
  lessorForm12Carrier : BrightonAdviceCarrierKind
  professionalAdviceEmailCarrier : BrightonAdviceCarrierKind
  professionalAdvicePhoneCarrier : BrightonAdviceCarrierKind

record BrightonAdviceCarrier : Set where
  constructor brightonAdviceCarrier
  field
    carrierKind : BrightonAdviceCarrierKind
    carrierReference : String
    temporalReference : String
    sourceRoleReference : String
    sourceReceipt : Set

open BrightonAdviceCarrier public

record ProfessionalTenancyAdviceReceipt : Set₁ where
  constructor professionalTenancyAdviceReceipt
  field
    adviceCarrier : BrightonAdviceCarrier
    adviceCarrierIsEmail : carrierKind adviceCarrier ≡ professionalAdviceEmailCarrier
    reviewedMatterMaterials : Set
    priorPhoneAdviceReferenced : Set
    adviceScopeReference : String
    adviceProviderReference : String
    professionalAdviceReceipt : Set

open ProfessionalTenancyAdviceReceipt public

record BrightonMatterAssertionBundle : Set₁ where
  constructor brightonMatterAssertionBundle
  field
    form11Carrier : BrightonAdviceCarrier
    form11CarrierExact : carrierKind form11Carrier ≡ matterForm11Carrier
    form16Carrier : BrightonAdviceCarrier
    form16CarrierExact : carrierKind form16Carrier ≡ matterForm16Carrier
    form12Carrier : BrightonAdviceCarrier
    form12CarrierExact : carrierKind form12Carrier ≡ lessorForm12Carrier

    mouldRoofRepairAssertion : Set
    conditionFitnessAssertion : Set
    noticeTimingAssertion : Set
    disputeResolutionProgression : Set

    assertionBundleReference : String

open BrightonMatterAssertionBundle public

record BrightonProfessionalAdviceLineage : Set₁ where
  constructor brightonProfessionalAdviceLineage
  field
    matterAssertions : BrightonMatterAssertionBundle
    professionalAdvice : ProfessionalTenancyAdviceReceipt

    -- Exact source/object identity remains explicit.  Merely discussing the
    -- same tenancy is not enough to weld advice to the matter packet.
    sameTenancyConsumerReceipt : Set
    adviceReviewsMatterPacketReceipt : Set
    chronologyReceipt : Set

    -- Advice may corroborate chronology/procedural engagement and may supply
    -- professional interpretation, but does not decide the underlying facts.
    adviceCorroboratesContemporaneousDispute : Set
    lineageReference : String

open BrightonProfessionalAdviceLineage public

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data MatterAssertionAutomaticallyTrue : Set where
data ProfessionalAdviceAutomaticallyFactFinding : Set where
data ProfessionalAdviceAutomaticallyTribunalFinding : Set where
data ProfessionalAdviceAutomaticallyStatutoryBreach : Set where
data AdviceAboutProcedureAutomaticallyPaysCausation : Set where
data Form12AutomaticallyProvesRetaliatoryMotive : Set where

aMatterAssertionDoesNotAutoBecomeTrue :
  MatterAssertionAutomaticallyTrue → ⊥
aMatterAssertionDoesNotAutoBecomeTrue ()

professionalAdviceDoesNotAutoBecomeFactFinding :
  ProfessionalAdviceAutomaticallyFactFinding → ⊥
professionalAdviceDoesNotAutoBecomeFactFinding ()

professionalAdviceDoesNotAutoBecomeTribunalFinding :
  ProfessionalAdviceAutomaticallyTribunalFinding → ⊥
professionalAdviceDoesNotAutoBecomeTribunalFinding ()

professionalAdviceDoesNotAutoBecomeStatutoryBreach :
  ProfessionalAdviceAutomaticallyStatutoryBreach → ⊥
professionalAdviceDoesNotAutoBecomeStatutoryBreach ()

proceduralAdviceDoesNotAutoPayCausation :
  AdviceAboutProcedureAutomaticallyPaysCausation → ⊥
proceduralAdviceDoesNotAutoPayCausation ()

form12DoesNotAutoProveRetaliatoryMotive :
  Form12AutomaticallyProvesRetaliatoryMotive → ⊥
form12DoesNotAutoProveRetaliatoryMotive ()

record BrightonProfessionalAdviceBoundary : Set where
  constructor brighton-professional-advice-boundary
  field
    matterAssertionsRemainAssertions : Bool
    professionalAdviceSeparateFromMatterFacts : Bool
    professionalAdviceSeparateFromTribunalFinding : Bool
    professionalAdviceSeparateFromStatutoryBreach : Bool
    proceduralAdviceSeparateFromCausation : Bool
    noticeTimingSeparateFromMotive : Bool

canonicalBrightonProfessionalAdviceBoundary : BrightonProfessionalAdviceBoundary
canonicalBrightonProfessionalAdviceBoundary =
  brighton-professional-advice-boundary
    true true true true true true
