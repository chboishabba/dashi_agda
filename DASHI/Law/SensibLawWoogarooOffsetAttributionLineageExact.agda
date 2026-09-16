module DASHI.Law.SensibLawWoogarooOffsetAttributionLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- WOOGAROO OFFSET ATTRIBUTION LINEAGE
--
-- Applies the canonical legal-claim provenance stages to the current offset
-- audit.  It deliberately does not create a parallel provenance calculus.
------------------------------------------------------------------------

record OffsetAttributedClaim : Set where
  constructor offset-attributed-claim
  field
    claimId : String
    proposition : String
    sourceOrAuthor : String
    stage : Provenance.LegalClaimProvenanceStage
    mayBeAttributedAsProjectFact : Bool
    mayBeAttributedAsAgencyFinding : Bool
    mayBeUsedAsCounselConclusion : Bool
    residual : String

open OffsetAttributedClaim public

commonwealthPolicyClaim : OffsetAttributedClaim
commonwealthPolicyClaim = offset-attributed-claim
  "offset-policy-risk-time-additionality"
  "The Commonwealth offsets framework treats residual impact, ecological equivalence, risk of loss, time to benefit, confidence, additionality and enforceability as relevant offset-quality coordinates."
  "Australian Government / EPBC Environmental Offsets Policy and Offset Assessment Guide"
  Provenance.externalSourceClaim
  false
  false
  false
  "Apply the policy criteria to the exact 2019/8575 project package; policy text alone does not prove project compliance or non-compliance."

qldHabitatAgeClaim : OffsetAttributedClaim
qldHabitatAgeClaim = offset-attributed-claim
  "qld-age-structure-habitat-function"
  "Queensland habitat guidance recognises that wildlife habitat value can depend on vegetation age/size and structural features such as hollows and fallen timber, and distinguishes mature/regrowth/revegetation states."
  "Queensland Government habitat/regrowth guidance"
  Provenance.externalSourceClaim
  false
  false
  false
  "Do not attribute this general ecological proposition to the proponent; same-object application to Woogaroo and any offset site remains open."

publicOffsetCritique : OffsetAttributedClaim
publicOffsetCritique = offset-attributed-claim
  "2019-8575-public-offset-critique"
  "A public submission responding to EPBC 2019/8575 alleges distant offset sites, ecological differences, mature-habitat mismatch, monitoring deficiencies and local-population concerns."
  "public submission responding to EPBC 2019/8575"
  Provenance.secondarySourceInterpretation
  false
  false
  false
  "Acquire or independently verify the exact proponent offset package before promoting any allegation to project fact."

woogarooVsOffsetRiskInference : OffsetAttributedClaim
woogarooVsOffsetRiskInference = offset-attributed-claim
  "woogaroo-offset-risk-loss-comparison"
  "If Woogaroo habitat is under high development pressure while an offset parcel is already protected or at low baseline loss risk, raw hectares may overstate additional avoided-loss gain."
  "DASHI cross-source inference from Commonwealth offset policy plus public/official land-use context"
  Provenance.crossSourceInference
  false
  false
  false
  "Needs exact tenure, planning constraints, existing protection and risk-of-loss values for each offset parcel."

matureVsPlantedInference : OffsetAttributedClaim
matureVsPlantedInference = offset-attributed-claim
  "mature-vs-planted-offset-equivalence"
  "Existing mature connected habitat and newly planted/restored habitat are not automatically functionally equivalent because ecological structure, species use and time-to-benefit can differ."
  "DASHI cross-source inference from Commonwealth offset policy and Queensland habitat guidance"
  Provenance.crossSourceInference
  false
  false
  false
  "Needs project-specific age, structure, quality, species-use and time-to-benefit evidence for both impact and offset sites."

protectedEstateProximityInference : OffsetAttributedClaim
protectedEstateProximityInference = offset-attributed-claim
  "protected-estate-connectivity-value"
  "If the impacted habitat functionally links existing protected/conservation estate, that connectivity may be an impacted ecological attribute requiring same-object treatment in the offset analysis."
  "DASHI cross-source inference from official conservation/planning context plus offset-policy same-attribute discipline"
  Provenance.crossSourceInference
  false
  false
  false
  "Requires exact geospatial and ecological proof of the functional linkage; proximity alone does not pay the proposition."

record OffsetAttributionBoundary : Set where
  constructor offset-attribution-boundary
  field
    submissionDoesNotBecomeProjectFact : Bool
    policyDoesNotBecomeAgencyFinding : Bool
    generalEcologyDoesNotBecomeSameParcelFact : Bool
    crossSourceInferenceNotAttributedToAnyOneSource : Bool
    attributionDoesNotCreateTruth : Bool
    attributionDoesNotCreateLegalAuthority : Bool
    attributionDoesNotCreateApplicability : Bool
    counselConclusionNotPreempted : Bool

offsetAttributionBoundary : OffsetAttributionBoundary
offsetAttributionBoundary = offset-attribution-boundary
  true true true true true true true true
