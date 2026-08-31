module DASHI.Governance.ReceptionPathPromotionExact where

------------------------------------------------------------------------
-- RECEPTION PATH PROMOTION
--
-- A path can be composable without its composite being licensed as a stronger
-- genealogy claim.  Promotion therefore requires path-level receipts rather
-- than inheriting the strongest relation/evidence label from one edge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.ReceptionRelationEvidenceTemporalGraphExact as Graph

record ReceptionPathPromotionReceipt : Set where
  constructor reception-path-promotion-receipt
  field
    path : Graph.ComposableReceptionPair
    bothEdgesSourceMatched : Bool
    temporalOrderSupported : Bool
    semanticTransportChecked : Bool
    institutionalTransportChecked : Bool
    directInfluenceEstablished : Bool
    promotedRelation : Graph.ReceptionRelationKind
    boundedReading : String

open ReceptionPathPromotionReceipt public

citationThenReinterpretationReceipt : ReceptionPathPromotionReceipt
citationThenReinterpretationReceipt = reception-path-promotion-receipt
  Graph.citationThenReinterpretation
  true true true false false
  Graph.explicitReinterpretation
  "The composable direct-citation then reinterpretation path supports a bounded reinterpretation reading; it does not by itself establish continuous institutional transmission or direct influence on every later use."

------------------------------------------------------------------------
-- No automatic transitive strengthening.
------------------------------------------------------------------------

data ComposablePathPromotesDirectInfluence : Set where

data TwoStrongEdgesPromoteInstitutionalContinuity : Set where

data CitationThenReinterpretationPromotesMeaningIdentity : Set where

data PathExistencePromotesUniqueGenealogy : Set where

composablePathDoesNotPromoteDirectInfluence :
  ComposablePathPromotesDirectInfluence -> ⊥
composablePathDoesNotPromoteDirectInfluence ()

twoStrongEdgesDoNotPromoteInstitutionalContinuity :
  TwoStrongEdgesPromoteInstitutionalContinuity -> ⊥
twoStrongEdgesDoNotPromoteInstitutionalContinuity ()

citationThenReinterpretationDoesNotPromoteMeaningIdentity :
  CitationThenReinterpretationPromotesMeaningIdentity -> ⊥
citationThenReinterpretationDoesNotPromoteMeaningIdentity ()

pathExistenceDoesNotPromoteUniqueGenealogy : PathExistencePromotesUniqueGenealogy -> ⊥
pathExistenceDoesNotPromoteUniqueGenealogy ()

record ReceptionPathPromotionBoundary : Set where
  constructor reception-path-promotion-boundary
  field
    composabilityEqualsDirectInfluence : Bool
    strongEdgesGuaranteeInstitutionalContinuity : Bool
    reinterpretationPreservesMeaningIdentity : Bool
    pathExistenceMakesGenealogyUnique : Bool
    pathLevelPromotionMayBeReceiptBearing : Bool

canonicalReceptionPathPromotionBoundary : ReceptionPathPromotionBoundary
canonicalReceptionPathPromotionBoundary =
  reception-path-promotion-boundary false false false false true
