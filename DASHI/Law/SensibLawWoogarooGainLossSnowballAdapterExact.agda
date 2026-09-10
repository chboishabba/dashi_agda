module DASHI.Law.SensibLawWoogarooGainLossSnowballAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.DisruptionBenefitHypothesisExact as Benefit
import DASHI.Core.ActorBenefitVisibilityDisruptionIntersectionExact as Actor
import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- WOOGAROO GAIN / LOSS x SNOWBALL ADAPTER
--
-- Reuses the Amy/disruption-benefit discipline: identifying a beneficiary or
-- burden-bearer is evidence about distribution, not motive, perpetration,
-- corruption, coordination or legal validity.
--
-- Snowball discipline: evidence may be acquired out of legal dependency order
-- and retained.  Acquiring a later DA/works receipt does not pay an earlier
-- federal, NCA, merits, same-parcel or contravention consumer by itself.
------------------------------------------------------------------------

data DistributionDirection : Set where
  gain : DistributionDirection
  loss : DistributionDirection
  exposure : DistributionDirection
  optionValue : DistributionDirection
  unresolvedDistribution : DistributionDirection

data RealisationStage : Set where
  approvedEntitlement : RealisationStage
  executableSubjectToOtherLaw : RealisationStage
  realisedOutcome : RealisationStage
  contingentFutureBenefit : RealisationStage
  contingentFutureBurden : RealisationStage
  unknownRealisation : RealisationStage

record DistributionCoordinate : Set where
  constructor distribution-coordinate
  field
    holder : String
    direction : DistributionDirection
    object : String
    mechanism : String
    stage : RealisationStage
    provenance : Provenance.LegalClaimProvenanceStage
    sourceReference : String
    caseSpecificMotivePaid : Bool
    illegalityPaid : Bool

open DistributionCoordinate public

------------------------------------------------------------------------
-- Primary DA receipts supplied from Ipswich Development.i PDFs.
------------------------------------------------------------------------

developerPrecinctOption : DistributionCoordinate
developerPrecinctOption = distribution-coordinate
  "Springview / Kalina development proponent and relevant land interests"
  optionValue
  "approved precinct-plan / development-plan pathway"
  "6243/2023/LAP, 4272/2020/ADP and 5547/2020/ADP create local planning entitlements and sequencing optionality subject to other applicable law"
  approvedEntitlement
  Provenance.repositoryReconstruction
  "User-supplied Development.i application summaries dated 10 September 2026"
  false false

futureHousingSupply : DistributionCoordinate
futureHousingSupply = distribution-coordinate
  "future purchasers / residents"
  gain
  "potential residential lots and associated open-space / road / drainage framework"
  "4272/2020/ADP and 5547/2020/ADP describe residential subdivision outcomes if later implemented"
  contingentFutureBenefit
  Provenance.repositoryReconstruction
  "4272/2020/ADP and 5547/2020/ADP Development.i summaries"
  false false

publicNotificationOpportunity : DistributionCoordinate
publicNotificationOpportunity = distribution-coordinate
  "members of the public who would otherwise participate through statutory notification"
  loss
  "statutory local-planning public-notification opportunity for these recorded applications"
  "6243/2023/LAP, 4272/2020/ADP, 5547/2020/ADP, 9281/2024/OW and 9293/2024/OW each record Public Notification Required: No"
  realisedOutcome
  Provenance.repositoryReconstruction
  "User-supplied Development.i application summaries"
  false false

vegetationExposure : DistributionCoordinate
vegetationExposure = distribution-coordinate
  "vegetation / habitat within the exact operational-works footprint"
  exposure
  "approved exposure to vegetation clearing, earthworks and stormwater works"
  "9281/2024/OW expressly includes Vegetation Clearing; approval creates an executable local works entitlement subject to other applicable law"
  executableSubjectToOtherLaw
  Provenance.repositoryReconstruction
  "9281/2024/OW Development.i summary"
  false false

roadEarthworksExposure : DistributionCoordinate
roadEarthworksExposure = distribution-coordinate
  "land / habitat within Village 2 stages 1-4A works footprint"
  exposure
  "road work, drainage, stormwater and earthworks"
  "9293/2024/OW approves the listed operational works subject to other applicable law"
  executableSubjectToOtherLaw
  Provenance.repositoryReconstruction
  "9293/2024/OW Development.i summary"
  false false

federalDecisionStillOpen : DistributionCoordinate
federalDecisionStillOpen = distribution-coordinate
  "Commonwealth EPBC 2019/8575 merits consumer"
  unresolvedDistribution
  "approval/refusal outcome"
  "local approvals do not resolve the pending Commonwealth Part 9 decision; the delegate's decision period is extended to 1 October 2026"
  unknownRealisation
  Provenance.repositoryReconstruction
  "2019/8575 s 130(1A) extension notice"
  false false

------------------------------------------------------------------------
-- Amy-derived benefit discipline: benefit is not actor attribution.
------------------------------------------------------------------------

record DistributionBoundary : Set where
  constructor distribution-boundary
  field
    beneficiaryImpliesImproperMotive : Bool
    beneficiaryImpliesImproperMotiveIsFalse : beneficiaryImpliesImproperMotive ≡ false
    approvalImpliesRealisedProfit : Bool
    approvalImpliesRealisedProfitIsFalse : approvalImpliesRealisedProfit ≡ false
    burdenImpliesUnlawfulness : Bool
    burdenImpliesUnlawfulnessIsFalse : burdenImpliesUnlawfulness ≡ false
    noPublicNotificationMeansNoConsultationOfAnyKind : Bool
    noPublicNotificationMeansNoConsultationOfAnyKindIsFalse : noPublicNotificationMeansNoConsultationOfAnyKind ≡ false
    localApprovalPaysFederalApproval : Bool
    localApprovalPaysFederalApprovalIsFalse : localApprovalPaysFederalApproval ≡ false
    worksApprovalProvesClearingOccurred : Bool
    worksApprovalProvesClearingOccurredIsFalse : worksApprovalProvesClearingOccurred ≡ false

canonicalDistributionBoundary : DistributionBoundary
canonicalDistributionBoundary = distribution-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Snowball acquisition/payment separation.
------------------------------------------------------------------------

data SnowballEvidenceAtom : Set where
  precinctApprovalAtom : SnowballEvidenceAtom
  village2ADPAtom : SnowballEvidenceAtom
  village3ADPAtom : SnowballEvidenceAtom
  vegetationClearingOWAtom : SnowballEvidenceAtom
  roadEarthworksOWAtom : SnowballEvidenceAtom
  federalDeadlineAtom : SnowballEvidenceAtom
  exactWorksPolygonAtom : SnowballEvidenceAtom
  actualCommencementAtom : SnowballEvidenceAtom
  s13EssentialityAtom : SnowballEvidenceAtom
  s102DetrimentalEffectAtom : SnowballEvidenceAtom
  contraventionAtom : SnowballEvidenceAtom

record SnowballAcquisitionState : Set where
  constructor snowball-acquisition-state
  field
    acquired : SnowballEvidenceAtom → Bool

open SnowballAcquisitionState public

currentAcquisition : SnowballAcquisitionState
currentAcquisition = snowball-acquisition-state λ where
  precinctApprovalAtom → true
  village2ADPAtom → true
  village3ADPAtom → true
  vegetationClearingOWAtom → true
  roadEarthworksOWAtom → true
  federalDeadlineAtom → true
  exactWorksPolygonAtom → false
  actualCommencementAtom → false
  s13EssentialityAtom → false
  s102DetrimentalEffectAtom → false
  contraventionAtom → false

record PaymentBoundary : Set where
  constructor payment-boundary
  field
    laterWorksReceiptPaysS13Essentiality : Bool
    laterWorksReceiptPaysS13EssentialityIsFalse : laterWorksReceiptPaysS13Essentiality ≡ false
    worksApprovalPaysS102DetrimentalEffect : Bool
    worksApprovalPaysS102DetrimentalEffectIsFalse : worksApprovalPaysS102DetrimentalEffect ≡ false
    approvalPaysContravention : Bool
    approvalPaysContraventionIsFalse : approvalPaysContravention ≡ false
    federalDeadlinePaysRefusal : Bool
    federalDeadlinePaysRefusalIsFalse : federalDeadlinePaysRefusal ≡ false
    laterEvidenceMayBeRetainedBeforeEarlierConsumerPaid : Bool
    laterEvidenceMayBeRetainedBeforeEarlierConsumerPaidIsTrue : laterEvidenceMayBeRetainedBeforeEarlierConsumerPaid ≡ true

snowballPaymentBoundary : PaymentBoundary
snowballPaymentBoundary = payment-boundary
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Distributional questions worth handing to counsel/economics/ecology.
------------------------------------------------------------------------

record DistributionResidual : Set where
  constructor distribution-residual
  field
    question : String
    evidenceNeeded : String
    status : String

open DistributionResidual public

whoCapturesDevelopmentValue : DistributionResidual
whoCapturesDevelopmentValue = distribution-residual
  "Which entities actually capture land-value, development, construction or financing gains from the approved Springview/Kalina sequence?"
  "current ownership, development agreements, option/finance arrangements, project entities and realised transaction data"
  "OPEN — approvals establish option/entitlement value, not realised profit or beneficiary identity beyond the named project/proponent interests."

whoBearsEcologicalLoss : DistributionResidual
whoBearsEcologicalLoss = distribution-residual
  "Which protected species, local populations, corridor functions and mature-habitat attributes bear loss if the approved operational works are exercised?"
  "exact 9281/9293 works polygons x habitat/species/corridor layers x clearing sequence x before/after condition"
  "OPEN — vegetation-clearing exposure is source-paid; exact ecological loss and magnitude are not."

whoBearsParticipationLoss : DistributionResidual
whoBearsParticipationLoss = distribution-residual
  "What participation opportunities were legally available despite Public Notification Required: No, and which groups actually received or lacked notice/consultation?"
  "applicable planning instrument, referral/consultation records, notices, council/proponent engagement chronology"
  "PARTIAL — absence of statutory public notification is source-paid; absence of all consultation is not."

whoPaysOffsetAndComplianceCosts : DistributionResidual
whoPaysOffsetAndComplianceCosts = distribution-residual
  "Who bears offset, habitat-management, infrastructure and compliance costs if federal approval is conditioned?"
  "final EPBC conditions / offset package / development agreements / cost allocation"
  "OPEN — do not infer from planning approvals."
