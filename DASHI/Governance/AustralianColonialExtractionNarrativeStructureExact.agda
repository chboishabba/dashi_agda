module DASHI.Governance.AustralianColonialExtractionNarrativeStructureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy

-- Distinct stages: adjacency does not manufacture a missing stage.
data ExtractionStage : Set where
  countryLand : ExtractionStage
  legalAdministrativeControl : ExtractionStage
  labourRelation : ExtractionStage
  physicalExtraction : ExtractionStage
  commodityOwnership : ExtractionStage
  credit : ExtractionStage
  insurance : ExtractionStage
  shipping : ExtractionStage
  sale : ExtractionStage
  profit : ExtractionStage
  remittance : ExtractionStage
  inheritanceProbate : ExtractionStage

data PaymentStatus : Set where paid unpaid : PaymentStatus

record StageReceipt : Set where
  constructor stage-receipt
  field
    from to : ExtractionStage
    grade : Genealogy.EvidenceGrade
    finding : String
    status : PaymentStatus
open StageReceipt public

marketCredit : StageReceipt
marketCredit = stage-receipt sale credit Genealogy.gradeB
  "Source-backed merchant and banking intermediation at bounded historical scope." paid

marketShipping : StageReceipt
marketShipping = stage-receipt sale shipping Genealogy.gradeB
  "Source-backed Australian gold purchasing and shipping through agents at bounded scope." paid

shippingRemittance : StageReceipt
shippingRemittance = stage-receipt shipping remittance Genealogy.gradeC
  "Exact consignment-to-account remittance remains an acquisition debt." unpaid

profitProbate : StageReceipt
profitProbate = stage-receipt profit inheritanceProbate Genealogy.gradeC
  "Probate accumulation remains an acquisition debt and is not inferred from merchant activity." unpaid

weakestGrade : Genealogy.EvidenceGrade → Genealogy.EvidenceGrade → Genealogy.EvidenceGrade
weakestGrade Genealogy.gradeE _ = Genealogy.gradeE
weakestGrade _ Genealogy.gradeE = Genealogy.gradeE
weakestGrade Genealogy.gradeD _ = Genealogy.gradeD
weakestGrade _ Genealogy.gradeD = Genealogy.gradeD
weakestGrade Genealogy.gradeC _ = Genealogy.gradeC
weakestGrade _ Genealogy.gradeC = Genealogy.gradeC
weakestGrade Genealogy.gradeB _ = Genealogy.gradeB
weakestGrade _ Genealogy.gradeB = Genealogy.gradeB
weakestGrade Genealogy.gradeA Genealogy.gradeA = Genealogy.gradeA

record ComposedPath : Set where
  constructor composed-path
  field
    first second : StageReceipt
    pathGrade : Genealogy.EvidenceGrade
open ComposedPath public

composeStages : StageReceipt → StageReceipt → ComposedPath
composeStages x y = composed-path x y (weakestGrade (grade x) (grade y))

marketIntermediationPath : ComposedPath
marketIntermediationPath = composeStages marketCredit marketShipping

record ExtractionBoundary : Set where
  constructor extraction-boundary
  field
    legalControlImpliesExtraction : Bool
    marketPresenceImpliesLabourRelation : Bool
    commodityPurchaseImpliesProduction : Bool
    shippingImpliesProfit : Bool
    merchantActivityImpliesProbateAccumulation : Bool
    weakestEdgeAuthorityPreserved : Bool
    edgeLocalProvenanceRequired : Bool
open ExtractionBoundary public

canonicalExtractionBoundary : ExtractionBoundary
canonicalExtractionBoundary = extraction-boundary false false false false false true true
