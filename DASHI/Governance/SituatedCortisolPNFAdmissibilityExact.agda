module DASHI.Governance.SituatedCortisolPNFAdmissibilityExact where

-- Original DASHI fail-closed bridge. This is a proof-obligation interface,
-- NOT an implementation of canonical PNF integer promotion or ITIR.
-- Posterior concentration (or entropy/uncertainty cutoff) alone is never
-- a causal identification or legal liability proof.
-- Legal owner: case-specific jurisdictional rules and adjudication.
-- Physiology owner: actual validated person-time cortisol data.
-- Crenshaw: conceptual situated institutional interpretation, not
-- authorship of this arithmetic or a cortisol attribution model.
open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Promotion.MeasurementProxyBoundaryCore as Proxy
import DASHI.Governance.SituatedCortisolTrajectoryAdmissionExact as Personal

data ClaimClass : Set where
  descriptiveBiomarker causalInstitutionalHarm
  clinicalDiagnosis enforceableLegalRemedy : ClaimClass

data ProofStage : Set where
  unconfirmedCandidate measuredObservation
  modeledInference causallyIdentified legallyAdjudicated : ProofStage

-- One simple exact uncertainty cap is modelled with Nats.
-- It is NOT Shannon entropy, a posterior density, or a legal threshold.
record FiniteUncertaintyControl : Set₁ where
  constructor finite-uncertainty-control
  field
    ambiguityScore : Nat
    announcedCap : Nat
    scoreBelowCap : ambiguityScore ≤ announcedCap
    modelAssumptionReview : Set

open FiniteUncertaintyControl public

-- Even zero residual ambiguity about a measured pattern does not
-- answer which of two possible institutional mechanisms produced it.
data AttributionWorld : Set where
  independentlyOccurred institutionContributed : AttributionWorld

measurementValue : AttributionWorld → Nat
measurementValue _ = 7

causalAttribution : AttributionWorld → Bool
causalAttribution independentlyOccurred = false
causalAttribution institutionContributed = true

sameBiomarkerDifferentCausation :
  NF.NonFactorabilityWitness measurementValue causalAttribution
sameBiomarkerDifferentCausation =
  NF.nonFactorabilityWitness
    independentlyOccurred institutionContributed refl (λ ())

pointIdentifiedBiomarkerDoesNotIdentifyCause :
  NF.FactorsThrough measurementValue causalAttribution → ⊥
pointIdentifiedBiomarkerDoesNotIdentifyCause =
  NF.witnessRulesOutEveryFlatFactorisation
    sameBiomarkerDifferentCausation

-- External evidence obligations are parametrised; their inhabitance
-- cannot be inferred from a scalar score or a citation to the report.
record ExternalGovernanceAudit
  (Person Case : Set) : Set₁ where
  field
    authenticatedAssay : Person → Set
    subjectTimeMatched : Person → Set
    independentlyValidatedModel : Person → Set
    alternativeCausesReviewed : Person → Case → Set
    defendantSpecificMechanism : Person → Case → Set
    validatedCounterfactualComparison : Person → Case → Set
    firstPersonAccountRespected : Person → Set
    institutionalSourceProvenance : Case → Set
    jurisdictionAndLegalElementsReviewed : Case → Set
    legallyAuthorisedDetermination : Case → Set

open ExternalGovernanceAudit public

record SourcePaidCausalFinding
  {Person Case : Set}
  (audit : ExternalGovernanceAudit Person Case)
  (person : Person) (legalCase : Case) : Set where
  constructor source-paid-causal-finding
  field
    assay : authenticatedAssay audit person
    samePersonTime : subjectTimeMatched audit person
    predictiveCheck : independentlyValidatedModel audit person
    alternatives : alternativeCausesReviewed audit person legalCase
    originalMechanism : defendantSpecificMechanism audit person legalCase
    originalCounterfactual :
      validatedCounterfactualComparison audit person legalCase
    accountAndConsent : firstPersonAccountRespected audit person
    institutionalSource : institutionalSourceProvenance audit legalCase

open SourcePaidCausalFinding public

record SeparatelyAdjudicatedLegalClaim
  {Person Case : Set}
  (audit : ExternalGovernanceAudit Person Case)
  (person : Person) (legalCase : Case) : Set where
  constructor separately-adjudicated-legal-claim
  field
    sourcePaidFinding : SourcePaidCausalFinding audit person legalCase
    jurisdictionPaid : jurisdictionAndLegalElementsReviewed audit legalCase
    judicialAuthorityPaid : legallyAuthorisedDetermination audit legalCase

open SeparatelyAdjudicatedLegalClaim public

causalFindingRequiresCounterfactual :
  ∀ {Person Case : Set}
    {audit : ExternalGovernanceAudit Person Case}
    {person : Person} {legalCase : Case} →
  SourcePaidCausalFinding audit person legalCase →
  validatedCounterfactualComparison audit person legalCase
causalFindingRequiresCounterfactual = originalCounterfactual

causalFindingRequiresSubjectVoice :
  ∀ {Person Case : Set}
    {audit : ExternalGovernanceAudit Person Case}
    {person : Person} {legalCase : Case} →
  SourcePaidCausalFinding audit person legalCase →
  firstPersonAccountRespected audit person
causalFindingRequiresSubjectVoice = accountAndConsent

legalFindingRequiresLegalAuthority :
  ∀ {Person Case : Set}
    {audit : ExternalGovernanceAudit Person Case}
    {person : Person} {legalCase : Case} →
  SeparatelyAdjudicatedLegalClaim audit person legalCase →
  legallyAuthorisedDetermination audit legalCase
legalFindingRequiresLegalAuthority = judicialAuthorityPaid

-- Preserve the existing measurement/proxy/cause separation.
measurementProxyDoesNotEstablishCausation :
  Proxy.proxyIsNotCause Proxy.canonicalMeasurementProxyBoundary ≡ true
measurementProxyDoesNotEstablishCausation = refl

-- The proposed deltaSigma is an *unpaid* named obstruction surface.
-- Neither uncertainty score nor a spectral transport defect has been
-- shown to be equivalent to legal admissibility or to a causal effect.
data DefectMeaning : Set where
  modelResidual causalIdentificationGap legalAdmissibilityGap : DefectMeaning

modelDefectNotLegalAdmissibility :
  modelResidual ≡ legalAdmissibilityGap → ⊥
modelDefectNotLegalAdmissibility ()
