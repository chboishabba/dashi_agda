module DASHI.Law.FascismAtrocitySourceCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.GazaGenocideHerzogZionismSourceReceiptsExact as Source
import FascisticSystem as Fascist

------------------------------------------------------------------------
-- Cross-pollination boundary: atrocity/genocide/ideology source propositions
-- may motivate investigation of fascistic structural coordinates, but they do
-- not by themselves instantiate the repo's empirical/political fascism label.
------------------------------------------------------------------------

data FascismFeature : Set where
  distinctionErasure
  provenanceWeaponisation
  collectiveGuiltTransport
  terminalisation
  asymmetricRouting
  coerciveContraction : FascismFeature

record FeatureReceipt : Set where
  constructor featureReceipt
  field
    feature : FascismFeature
    sourceReference : String
    empiricalClosure : Bool

open FeatureReceipt public

record FascismAssessmentFibre : Set where
  constructor fascismAssessmentFibre
  field
    erasureReceipt : FeatureReceipt
    provenanceReceipt : FeatureReceipt
    collectiveGuiltReceipt : FeatureReceipt
    terminalisationReceipt : FeatureReceipt
    asymmetricRoutingReceipt : FeatureReceipt
    contractionReceipt : FeatureReceipt
    assessmentReference : String

open FascismAssessmentFibre public

openFeature : FascismFeature → String → FeatureReceipt
openFeature f ref = featureReceipt f ref false

canonicalSourceOnlyAssessment : FascismAssessmentFibre
canonicalSourceOnlyAssessment = fascismAssessmentFibre
  (openFeature distinctionErasure "requires independent empirical bridge")
  (openFeature provenanceWeaponisation "requires independent empirical bridge")
  (openFeature collectiveGuiltTransport "requires independent empirical bridge")
  (openFeature terminalisation "requires independent empirical bridge")
  (openFeature asymmetricRouting "requires independent empirical bridge")
  (openFeature coerciveContraction "requires proper-contraction witness, not rhetoric")
  "UN genocide/incitement findings are source receipts, not an automatic fascism diagnosis"

------------------------------------------------------------------------
-- Source proposition to investigation-target routing.
------------------------------------------------------------------------

data CrossPollinationClaim : Set where
  genocideFindingInvitesFascismFeatureAudit
  herzogIncitementFindingInvitesCommandIdeologyAudit
  historicalTerrorismInvitesGenealogyAudit
  fascismDiagnosisClosed : CrossPollinationClaim

data CrossPollinationProducer : Set where
  sourceReceiptProducer
  featureSpecificEmpiricalReceiptProducer
  commandIdeologyBridgeProducer
  genealogyReceiptProducer
  fullFascismAssessmentProducer : CrossPollinationProducer

reverseCrossPollination : CrossPollinationClaim → CrossPollinationProducer
reverseCrossPollination genocideFindingInvitesFascismFeatureAudit = sourceReceiptProducer
reverseCrossPollination herzogIncitementFindingInvitesCommandIdeologyAudit = commandIdeologyBridgeProducer
reverseCrossPollination historicalTerrorismInvitesGenealogyAudit = genealogyReceiptProducer
reverseCrossPollination fascismDiagnosisClosed = fullFascismAssessmentProducer

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    genocideFindingImpliesFascism : Bool
    genocideFindingImpliesFascismIsFalse : genocideFindingImpliesFascism ≡ false
    incitementFindingImpliesEveryPoliceActionIdeological : Bool
    incitementFindingImpliesEveryPoliceActionIdeologicalIsFalse : incitementFindingImpliesEveryPoliceActionIdeological ≡ false
    historicalIrgunSternTerrorismImpliesAllZionismTerrorist : Bool
    historicalIrgunSternTerrorismImpliesAllZionismTerroristIsFalse : historicalIrgunSternTerrorismImpliesAllZionismTerrorist ≡ false
    structuralContractionImpliesPoliticalFascism : Bool
    structuralContractionImpliesPoliticalFascismIsFalse : structuralContractionImpliesPoliticalFascism ≡ false

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  crossPollinationBoundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- Reuse the existing fascism core's own honesty boundary: proper contraction
-- is mathematical structure only.  This adapter exposes that fact inside the
-- law/source lane without claiming a political diagnosis.
------------------------------------------------------------------------

record ProperContractionAdapter : Set₁ where
  constructor properContractionAdapter
  field
    projection : Fascist.Projection
    contraction : Fascist.ProperContraction projection
    empiricalPoliticalDiagnosisPromoted : Bool
    empiricalPoliticalDiagnosisPromotedIsFalse : empiricalPoliticalDiagnosisPromoted ≡ false

open ProperContractionAdapter public
