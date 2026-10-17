module DASHI.Economics.AIBISCircularFinancingSystemRisk20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

institutionalReportKind : Source.SourceKind
institutionalReportKind = Source.institutionalSource

bis2026Source : Source.AttributedSource
bis2026Source = Source.mkNoDOISource
  "Bank for International Settlements"
  "Annual Economic Report 2026 — Progress and peril"
  "BIS Annual Economic Report"
  "2026"
  "https://www.bis.org/publications/aer-2026/progress-peril"
  institutionalReportKind
  "institutional source identifying circular financing among hyperscalers, chip makers, AI labs and neoclouds; opaque private arrangements; outsourced data-centre structures; and credit/pledging vulnerabilities. Source does not establish fraud, insolvency or a sector-wide crash."
  Source.publicAttribution

record BISCircularFinancingObservation : Set where
  constructor bis-circular-financing-observation
  field
    circularFinancingMechanismObserved : Bool
    equityPurchaseCommitmentLoopObserved : Bool
    opaquePrivateArrangementsObserved : Bool
    thirdPartyDataCentreLeaseStructuresObserved : Bool
    multiplePledgeRiskMentioned : Bool
    sizeableSectorFinancingShareAttributed : Bool
    fraudEstablished : Bool
    insolvencyEstablished : Bool
    bubbleEstablished : Bool
    systemicCrisisEstablished : Bool
    source : Source.AttributedSource

open BISCircularFinancingObservation public

bis2026CircularFinancingObservation : BISCircularFinancingObservation
bis2026CircularFinancingObservation = bis-circular-financing-observation
  true true true true true true
  false false false false bis2026Source

institutionalMechanismClassPaid :
  (circularFinancingMechanismObserved bis2026CircularFinancingObservation ≡ true) ×
  (opaquePrivateArrangementsObserved bis2026CircularFinancingObservation ≡ true) ×
  (multiplePledgeRiskMentioned bis2026CircularFinancingObservation ≡ true)
institutionalMechanismClassPaid = refl , refl , refl

bubbleStillOpen : bubbleEstablished bis2026CircularFinancingObservation ≡ false
bubbleStillOpen = refl

data CircularFinancingImpliesFraudPermission : Set where
data PledgeRiskImpliesDuplicatePledgeFactPermission : Set where
data InstitutionalRiskObservationImpliesCrisisPermission : Set where

circularFinancingDoesNotCreateFraud : CircularFinancingImpliesFraudPermission → ⊥
circularFinancingDoesNotCreateFraud ()

pledgeRiskDoesNotCreateDuplicatePledgeFact : PledgeRiskImpliesDuplicatePledgeFactPermission → ⊥
pledgeRiskDoesNotCreateDuplicatePledgeFact ()

riskObservationDoesNotCreateCrisis : InstitutionalRiskObservationImpliesCrisisPermission → ⊥
riskObservationDoesNotCreateCrisis ()

boundary : String
boundary =
  "BIS 2026 independently recognises the AI-sector mechanism class that DASHI models as capital/revenue reflexivity: equity investment can be coupled to purchase commitments, data-centre financing can be outsourced through long-dated structures, and opaque arrangements can create credit/pledging vulnerabilities. BIS authority pays that institutional risk observation only. It does not turn a candidate graph edge into fraud, prove that any particular asset was pledged twice, establish insolvency, or establish an AI bubble/systemic crisis."