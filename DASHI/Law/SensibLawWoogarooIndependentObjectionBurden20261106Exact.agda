module DASHI.Law.SensibLawWoogarooIndependentObjectionBurden20261106Exact where

-- EPBC 2019/8575. Professional/community-original adversarial cut.
-- QUT: Monica Taylor, Rowena Maguire and Bridget Lewis, 12 March 2026.
-- QCC: Anthony Gough, Queensland Conservation Council, 12 March 2026.
-- Do not transfer their authorship into this mathematical reconciliation.
--
-- These source-authored submissions are INDEPENDENT of proponent
-- modelling as *opinions*, but (i) not every asserted underlying
-- observation is backed by its original receipt here, (ii) citations
-- to Possingham/Zdenek are not their same-project source submissions,
-- (iii) an independent opinion is not a court, agency or field finding.
--
-- Existing DASHI attribution, source dependency and #1276 adversarial
-- owners remain canonical. No ad hoc invention of professional evidence.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooKoalaPopulationConnectivitySnowballExact as OriginalAttribution
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as OriginalDependencies
import DASHI.Law.SensibLawWoogarooEPBC8575DualUseEvidenceMatrixExact as OriginalDualUse
import DASHI.Law.SensibLawWoogarooProponentEvidenceAdversarialAudit20261106Exact as Proponent
import DASHI.Law.SensibLawWoogarooAllSpeciesOAGSourceReconciliation20261106Exact as OAG

data OriginalSource : Set where
  qut20260312 qcc20260312 communityOriginal
    rspca2025 holdingTheLine2023 independentFieldOriginal
    proponentPD20260130 governmentDecision : OriginalSource

data Claim : Set where
  matureForestLoss climateRefugeLoss corridorSeverance
    populationViability cumulativeEffects indirectHeatImpacts
    limitedHollowSurvey residentKoalas rescueReturn
    vegetation21Percent irreplaceableRedZone
    area136Hectares surrounding500Ha
    OAGFutureBenefit full95BConsideration section95CReasoning
    approvedOffsetSpatialIdentity actualOffsetDeclaration : Claim

data ReceiptStage : Set where
  originalAuthoredSubmission originalOrganisationPublicReport
    originalIndependentCommissionedAnalysis primaryFieldObservation
    proponentModelAssertion officialRecord corroboratedSameSite
    unresolvedUnderlyingRecord : ReceiptStage

record ClaimReceipt : Set where
  constructor claim-receipt
  field
    source : OriginalSource
    proposition : Claim
    stage : ReceiptStage
    propositionText : String
    citation : String
    underlyingIndependentObservationPaid : Bool
    decisionMakerConsiderationPaid : Bool
open ClaimReceipt public

-- QUT signed submission: the ORIGINAL submission is in hand;
-- the statements about threatened ecology require their own original
-- same-site field/map evidence if the consumer needs observed truth.
qutCorridor : ClaimReceipt
qutCorridor = claim-receipt qut20260312 corridorSeverance
  originalAuthoredSubmission
  "QUT says the proposal disrupts movement and survival networks and lacks credible landscape-scale modelling."
  "Taylor, Maguire and Lewis, QUT School of Law submission, 12 March 2026, pp 2-3, paras 4,7"
  false false

qutClimate : ClaimReceipt
qutClimate = claim-receipt qut20260312 climateRefugeLoss
  originalAuthoredSubmission
  "QUT identifies shaded gullies, moisture and heat refuge as impacted functions not restored by a remote tree count."
  "QUT 12 March 2026, pp 2-3, paras 1,6-7"
  false false

qutCumulative : ClaimReceipt
qutCumulative = claim-receipt qut20260312 cumulativeEffects
  originalAuthoredSubmission
  "QUT raises 396 ha regional clearing over 10-15 years and 500 ha landscape block; verify original geospatial boundaries and project attribution."
  "QUT 12 March 2026, pp 3, paras 4-5"
  false false

qccConnectivity : ClaimReceipt
qccConnectivity = claim-receipt qcc20260312 corridorSeverance
  originalAuthoredSubmission
  "QCC describes the Woogaroo Creek-Opossum Creek habitat corridor and loss of mature local connectivity."
  "QCC submission, 12 March 2026, pp 2-4"
  false false

qccSurvey : ClaimReceipt
qccSurvey = claim-receipt qcc20260312 limitedHollowSurvey
  originalAuthoredSubmission
  "QCC challenges survey adequacy for hollow-dependent fauna and outdated survey effort."
  "QCC submission, 12 March 2026, p 2"
  false false

qccRescue : ClaimReceipt
qccRescue = claim-receipt qcc20260312 rescueReturn
  originalAuthoredSubmission
  "QCC reports that RSPCA treated and returned koalas. The original dated case records remain separate."
  "QCC submission, 12 March 2026, p 2"
  false false

qccLandscape : ClaimReceipt
qccLandscape = claim-receipt qcc20260312 vegetation21Percent
  originalAuthoredSubmission
  "QCC cites approximately 21 percent remaining Ipswich native vegetation and a 30-percent landscape heuristic; project polygon, denominator and cited commissioned reports require original join."
  "QCC submission, 12 March 2026, p 3; cited Holding the Line"
  false false

qccRedZone : ClaimReceipt
qccRedZone = claim-receipt qcc20260312 irreplaceableRedZone
  originalAuthoredSubmission
  "QCC argues high-value red-zone/irreplaceable habitat classification; full original zoning report and selected project polygon required."
  "QCC submission, 12 March 2026, pp 3-4"
  false false

-- Newly verified independent FIRST-PARTY records (not rephrased QCC):
-- RSPCA Queensland, Emma Lagoon, published 2 June 2025 and 11 April
-- 2025. In Nov 2024 Maximus and William received RSPCA treatment;
-- both later returned to Woogaroo Forest / bordering forest. RSPCA
-- says three koalas from the same broader area entered care, not all
-- three proved inside the exact EPBC 2019/8575 impact polygon.
rspcaMaximusDirectOriginal : ClaimReceipt
rspcaMaximusDirectOriginal = claim-receipt rspca2025 rescueReturn
  originalOrganisationPublicReport
  "RSPCA Queensland confirms Maximus (treated from Nov 2024) returned to Woogaroo Forest after six months' care; three koalas entered care from the same general area."
  "RSPCA Queensland / Emma Lagoon, 2 June 2025, Maximus the Koala returns to Woogaroo Forest"
  false false

rspcaWilliamDirectOriginal : ClaimReceipt
rspcaWilliamDirectOriginal = claim-receipt rspca2025 rescueReturn
  originalOrganisationPublicReport
  "RSPCA confirms William rescued Bellbird Park November 2024 and returned to a forest described as bordering Woogaroo Forest."
  "RSPCA Queensland / Emma Lagoon, 11 April 2025, William the Koala returns home"
  false false

-- Original professional source is now DIRECTLY accessible: 2023
-- QCC-commissioned Holding the Line report, by Shannon Mooney and
-- Andrew Davidson; Table 8 citing HLW 2021 maps Ipswich LGA 21%
-- remnant vegetation. It is NOT a new 2026 cover measurement, not
-- Woogaroo-polygon remnant proportion, and not a universal legally
-- binding 30% biological threshold.
holdingTheLineOriginal : ClaimReceipt
holdingTheLineOriginal = claim-receipt holdingTheLine2023 vegetation21Percent
  originalIndependentCommissionedAnalysis
  "Ipswich City LGA: 109315 ha total council area and 21 percent remnant vegetation according to Table 8, HLW 2021 source."
  "Mooney and Davidson, Holding the Line (QCC, version 2.0, 31 August 2023), Table 8 p31"
  false false

-- Explicit non-promotion: a full OAG numerical score and four-species
-- printed percentages do not by themselves witness the community/QUT
-- material functions below. At most they provide a projected offset
-- habitat/feature proxy, not a same-function, same-site ecological weld.
data EcologicalFunction : Set where
  existingMatureCanopy shadedHeatRefuge localMovementNetwork
    localPopulationViability seasonalForagingResource
    hollowBearingTreeStructure : EcologicalFunction

data CalculatorAttribute : Set where
  predictedQualityScore predictedPreferredTreeCount
    claimedCompensationPercent : CalculatorAttribute

data SameFunctionValidation : CalculatorAttribute → EcologicalFunction → Set where

noAutomaticMatureForestEquivalence :
  SameFunctionValidation predictedQualityScore existingMatureCanopy → ⊥
noAutomaticMatureForestEquivalence ()

noAutomaticCorridorEquivalence :
  SameFunctionValidation claimedCompensationPercent localMovementNetwork → ⊥
noAutomaticCorridorEquivalence ()

noAutomaticClimateRefugeEquivalence :
  SameFunctionValidation predictedPreferredTreeCount shadedHeatRefuge → ⊥
noAutomaticClimateRefugeEquivalence ()

-- The selected evidence ledger is not a mere catalogue: it bounds the
-- number of *source-authored* leads while providing zero fabricated
-- independent observation and decision-consequence receipts.
qutAndQccLeadCount : Nat
qutAndQccLeadCount = 3 + 5

eightSelectedLeads : qutAndQccLeadCount ≡ 8
eightSelectedLeads = refl

data UnpaidOriginal : Set where
  qutUnderlyingSiteGIS qccHoldingTheLine
    qccBioregionalZoningReport rspcaOriginalRecords
    residentKoalaObservationLog specialistCurrentFaunaSurvey
    signedApprovedOctoberOAMP full95BCommentPacket
    full95CRecommendation ministerConsiderationRecord
    originalSection19FDeclarations currentWorksMonitoring
    sourceExactCausalEcology : UnpaidOriginal

-- Prior independent and proponent proof owners are linked, not copied.
priorQUTAttribution = OriginalAttribution.qutCurrentSubmission
priorQCCAttribution = OriginalAttribution.qccCurrentSubmission
priorProponentAudit : Proponent.ProponentEvidenceReview
priorProponentAudit = Proponent.review Proponent.habitatConnectivity
priorOAGSourceMismatch : 18447 ≡ 18447
priorOAGSourceMismatch = OAG.mwwRegentRowSum
