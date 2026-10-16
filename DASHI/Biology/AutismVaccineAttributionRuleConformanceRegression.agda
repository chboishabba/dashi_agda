module DASHI.Biology.AutismVaccineAttributionRuleConformanceRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.AutismVaccineExternalSourceAtlasExact as Atlas
import DASHI.Biology.AutismVaccineAttributionRuleConformanceExact as C
import DASHI.Biology.AutismVaccineClaimPromotionAuditExact as Audit
import DASHI.Biology.AutismVaccineStrictBindingInstantiationExact as Binding

citationAndSourceIdentityDoNotCreateAuthorityRegression :
  C.citationCreatesProof C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
  × C.citationCreatesAuthority C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
citationAndSourceIdentityDoNotCreateAuthorityRegression = refl , refl

hbomSourceItselfDoesNotImportProofOrAuthority :
  Source.citationImportsProof Atlas.hbomberguyMeasuredResponseSource ≡ false
  × Source.citationCreatesAuthority Atlas.hbomberguyMeasuredResponseSource ≡ false
hbomSourceItselfDoesNotImportProofOrAuthority =
  C.canonicalHbombCitationImportsProofWitness , C.canonicalHbombCitationAuthorityWitness

supportPriorityCorrectnessRemainSeparateRegression :
  C.scientificSupportProvesPriority C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
  × C.priorityProvesCorrectness C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
supportPriorityCorrectnessRemainSeparateRegression = refl , refl

contactExposureDoesNotBecomeDerivationRegression :
  C.contactOrExposureProvesDerivation C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
  × C.contactOrExposureProvesPlagiarism C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
contactExposureDoesNotBecomeDerivationRegression = refl , refl

unknownAndUnpaidDoNotBecomeZeroRegression :
  C.unknownCoordinateEqualsZero C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
  × C.unpaidCoordinateEqualsZero C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
unknownAndUnpaidDoNotBecomeZeroRegression = refl , refl

sourceAndDASHISynthesisRemainSeparateRegression :
  C.externalSourceOwnsDASHISynthesis C.canonicalAutismVaccineAttributionRuleBoundary ≡ false
sourceAndDASHISynthesisRemainSeparateRegression = refl

hviidTypedClaimPaymentIsActuallyConsumed :
  Binding.EvidencePaysClaim Audit.hviid2019Receipt Audit.hbombMMRNoLinkClaim
hviidTypedClaimPaymentIsActuallyConsumed = C.canonicalHviidEvidenceClaimWitness

hviidTypedEstimandMatchIsActuallyConsumed :
  Binding.EvidenceMatchesEstimand Audit.hviid2019Receipt Binding.mmrAutismPopulationEstimand
hviidTypedEstimandMatchIsActuallyConsumed = C.canonicalHviidEstimandWitness
