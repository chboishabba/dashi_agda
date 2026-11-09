module DASHI.Law.SensibLawWoogarooAvonvalePriorDeclaration20261109Exact where

-- Primary source exact prior-protection ledger, 9 November 2026.
-- DIFFERENT ACTION: EPBC 2018/8347 Providence East/South
-- proponent compliance report (Saunders Havill, 13 March 2024).
-- The report's Appendix F reproduces ORIGINAL Queensland Department
-- of Resources section 19F(1) signed declaration notice of
-- 21 December 2022 (DAM 2022/002500, PMAV 2022/002505),
-- for lots 1 CSH1549 and 4/5/9/10 SP327519.
-- Original state notice is embedded in third-party published PDF;
-- certified registry/title search for current status remains OPEN.
--
-- SAME LANDHOLDING / DIFFERENT APPROVAL: preliminary PD v5
-- EPBC 2019/8575 (30 January 2026) Part A.i section 6.4 and
-- Avonvale OAMP Part A.iii attribute 168 ha new offset to
-- lots 2 SP330365, 3 SP327519, 1 RP75222, 98 CA31786,
-- 61 CA31716, and expressly call it balance land ADJACENT to
-- previously approved offset areas including EPBC 2018/8347.
--
-- Distinguishing lots is not proving polygons don't overlap,
-- that benefits are additional, or that prior conservation gains
-- cannot be shared. These are scientific, cadastral and legal
-- source gates: never infer double-crediting, financing, breach,
-- fraud, condition discharge or current declaration for 2019/8575.
-- Original QUT, QCC, RSPCA and other attributed owners preserved.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawWoogarooOffsetCandidateIdentityCollisionExact as Prior

data Matter : Set where
  providence20188347 springfield20198575 : Matter

data SourceClass : Set where
  governmentDirectOriginal
    governmentOriginalReproducedInProponentPDF
    proponent2024ComplianceReport
    proponent2026PreliminaryDocumentation : SourceClass

data ReceiptStage : Set where
  textVerifiedInOriginalPublishedDocument
    sourceAuthoredStatement unacquiredCurrentRegistryReceipt
    unacquiredExactPolygon : ReceiptStage

record PrimaryFact : Set where
  constructor primary-fact
  field
    matter : Matter
    sourceClass : SourceClass
    stage : ReceiptStage
    assertion : String
    primaryURL : String
open PrimaryFact public

existingStateDeclaration : PrimaryFact
existingStateDeclaration = primary-fact
  providence20188347 governmentOriginalReproducedInProponentPDF
  textVerifiedInOriginalPublishedDocument
  "21 December 2022 Department of Resources 19F decision 2022/002500 declares parts of Lot 1 CSH1549 and Lots 4,5,9,10 SP327519; PMAV 2022/002505."
  "https://www.stockland.com.au/globalassets/residential/qld/providence/offset-management-plan/providence-east-epbc-acr--year-1-13032024.pdf"

prior2024ComplianceClaim : PrimaryFact
prior2024ComplianceClaim = primary-fact
  providence20188347 proponent2024ComplianceReport
  sourceAuthoredStatement
  "2018/8347 approval condition 13a required >=183ha Avonvale and Cherry Gully secured pre-commencement; 2024 compliance report claims minister notified 23 December 2022."
  "https://www.stockland.com.au/globalassets/residential/qld/providence/offset-management-plan/providence-east-epbc-acr--year-1-13032024.pdf"

-- NEW official negative control from the SAME *older* Providence
-- approval, NOT a decision on Woogaroo 2019/8575.
-- The National EPA official directed-variations register states that
-- on 31 March 2025 the Minister directed a condition variation in
-- response to failure to secure an ONSITE conservation area on time
-- and continuing clearing absent approved management plans.
-- The signed original s143 variation is by Toni Hart on that date
-- for AW Bidco 6, EPBC 2018/8347. Its original effect changes
-- conditions 5,6,8,10,11,12,17,19,23, revokes 18 and 26,
-- and replaces the original Appendix B map. That enforcement does
-- NOT establish the previously declared 2022 Avonvale/Cherry Gully
-- s19F offset was itself unregistered or that Cherish 2019/8575 has
-- committed any breach. It *does* make historical performance and
-- earlier obligation status appropriate independent review subjects.

data AdministrativeOutcome : Set where
  federalDirectedVariation otherMatterOnly : AdministrativeOutcome

record OfficialAction : Set where
  constructor official-action
  field
    actionMatter : Matter
    outcome : AdministrativeOutcome
    decisionDayYYYYMMDD : Nat
    administrativeOrderMade : Bool
    courtJudgmentMade : Bool
    proves20198575Breach : Bool
open OfficialAction public

officialProvidenceVariation : OfficialAction
officialProvidenceVariation =
  official-action providence20188347 federalDirectedVariation
    20250331 true false false

signedOtherMatterVariation : PrimaryFact
signedOtherMatterVariation = primary-fact
  providence20188347 governmentDirectOriginal
  textVerifiedInOriginalPublishedDocument
  "Signed 31 March 2025 EPBC Act s143 directed conditions variation, Toni Hart, AW Bidco 6, EPBC 2018/8347; replaces site conditions and Appendix B map. Original government instrument available directly."
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/125d74c5-530f-f011-998a-00224811099e/2ab10dab-d681-4911-b881-cc99413f07b6?file=2018-8347-Variation-to-Conditions.pdf"

olderEnforcementNotThisCase :
  proves20198575Breach officialProvidenceVariation ≡ false
olderEnforcementNotThisCase = refl

olderVariationNotJudgment :
  courtJudgmentMade officialProvidenceVariation ≡ false
olderVariationNotJudgment = refl

later2026AdjacentClaim : PrimaryFact
later2026AdjacentClaim = primary-fact
  springfield20198575 proponent2026PreliminaryDocumentation
  sourceAuthoredStatement
  "New proposed 168ha Avonvale offset is balance land adjacent to existing offsets; listed on 2 SP330365, 3 SP327519, 1 RP75222, 98 CA31786, 61 CA31716."
  "Original Springfield PD v5 30 January 2026, Part A.i section 6.4 and Part A.iii Avonvale OAMP"

data PriorParcel : Set where
  oldLot1CSH1549 oldLot4SP327519 oldLot5SP327519
    oldLot9SP327519 oldLot10SP327519 : PriorParcel

data ProposedParcel : Set where
  newLot2SP330365 newLot3SP327519 newLot1RP75222
    newLot98CA31786 newLot61CA31716 : ProposedParcel

-- The two finite cadastral lists have distinguishable references
-- and are for different action/offset records. This is not proof of
-- a topological no-overlap without both ORIGINAL signed polygons.
data SpatialProposition : Set where
  sameNamedLandholding nominalLotListsDiffer
    exactAreaOverlap independentlyAdditionalGain : SpatialProposition

record AuditState : Set where
  constructor audit-state
  field
    priorDeclarationPrimaryTextFound : Bool
    priorDeclarationCurrentlyRegisteredConfirmed : Bool
    laterPlanExpresslyClaimsAdjacentBalanceLand : Bool
    exactOverlapPolygonPaid : Bool
    priorManagementObligationCreditAllocationPaid : Bool
    independentAdditionalGainDemonstrated : Bool
open AuditState public

avonvaleAuditedState : AuditState
avonvaleAuditedState = audit-state true false true false false false

priorDeclarationSourceFound :
  priorDeclarationPrimaryTextFound avonvaleAuditedState ≡ true
priorDeclarationSourceFound = refl

laterAdjacentClaimSourceFound :
  laterPlanExpresslyClaimsAdjacentBalanceLand avonvaleAuditedState ≡ true
laterAdjacentClaimSourceFound = refl

doubleCreditingNotEstablished :
  exactOverlapPolygonPaid avonvaleAuditedState ≡ false
doubleCreditingNotEstablished = refl

priorOwnerNotReplaced : Prior.CandidateReceipt
priorOwnerNotReplaced = Prior.otherAvonvaleApproval
