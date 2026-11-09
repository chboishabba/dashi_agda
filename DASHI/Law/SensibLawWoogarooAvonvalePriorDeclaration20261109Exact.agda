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
