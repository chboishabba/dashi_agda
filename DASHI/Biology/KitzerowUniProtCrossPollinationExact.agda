module DASHI.Biology.KitzerowUniProtCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ExternalBiologyEvidenceCore as External
import DASHI.Biology.ExternalBiologyConsumerAdmissionExact as Admission
import DASHI.Biology.UniProtExternalKnowledgeExact as UniProt
import DASHI.Biology.KitzerowBH4EvidenceAtlasExact as Atlas
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- KITZEROW <-> EXTERNAL BIOLOGY CROSS-POLLINATION
--
-- The external database layer can pay bounded biochemical nodes in the atlas,
-- but it cannot manufacture chronology, contact, attribution or whole-model
-- confirmation.  This is deliberately a bridge between owners, not a merge.
------------------------------------------------------------------------

record KitzerowExternalEvidenceAdapter : Set where
  constructor kitzerowExternalEvidenceAdapter
  field
    adapterId : String
    externalClaim : External.BiologicalClaim
    atlasTarget : Atlas.RelationTarget
    boundedContribution : String
    externalClaimPaysBoundedNode : Bool
    externalClaimPaysBoundedNodeIsTrue :
      externalClaimPaysBoundedNode ≡ true
    externalClaimConfirmsWholeGraph : Bool
    externalClaimConfirmsWholeGraphIsFalse :
      externalClaimConfirmsWholeGraph ≡ false
    externalClaimCreatesPriority : Bool
    externalClaimCreatesPriorityIsFalse :
      externalClaimCreatesPriority ≡ false
    externalClaimCreatesContactEvidence : Bool
    externalClaimCreatesContactEvidenceIsFalse :
      externalClaimCreatesContactEvidence ≡ false
    externalClaimCreatesAttributionBreach : Bool
    externalClaimCreatesAttributionBreachIsFalse :
      externalClaimCreatesAttributionBreach ≡ false

open KitzerowExternalEvidenceAdapter public

qdprBH4AvailabilityAdapter : KitzerowExternalEvidenceAdapter
qdprBH4AvailabilityAdapter =
  kitzerowExternalEvidenceAdapter
    "KIT-UNIPROT-QDPR-BH4"
    UniProt.qdprBH4RegenerationClaim
    Atlas.bh4Availability
    "QDPR/P09417 pays a bounded external biochemical witness that BH4 regeneration is a real annotated reaction-level object; it does not identify BH4 dysregulation as the upstream cause of autism or validate the complete Kitzerow cascade."
    true refl
    false refl
    false refl
    false refl
    false refl

qdprAtlasConsumerAssessment : Admission.ConsumerAssessment
qdprAtlasConsumerAssessment =
  Admission.mkAssessment
    "ASSESS-KIT-QDPR-BH4-NODE"
    UniProt.qdprBH4RegenerationClaim
    Admission.mechanisticModelConsumer
    Admission.curatedLiteratureGrade
    Admission.insufficient
    "The QDPR claim is usable as one biochemical node inside the atlas, but is insufficient as a disease-level mechanistic proof."
    "A same-object chain from measured BH4/QDPR state through the proposed allocator and autism-relevant downstream phenotype remains required."

record KitzerowUniProtBoundary : Set where
  constructor kitzerowUniProtBoundary
  field
    qdprNodeSupportConfirmsWholeGraph : Bool
    qdprNodeSupportConfirmsWholeGraphIsFalse :
      qdprNodeSupportConfirmsWholeGraph ≡ false
    uniprotAnnotationEstablishesKitzerowPriority : Bool
    uniprotAnnotationEstablishesKitzerowPriorityIsFalse :
      uniprotAnnotationEstablishesKitzerowPriority ≡ false
    uniprotAnnotationEstablishesContact : Bool
    uniprotAnnotationEstablishesContactIsFalse :
      uniprotAnnotationEstablishesContact ≡ false
    uniprotAnnotationEstablishesAttributionBreach : Bool
    uniprotAnnotationEstablishesAttributionBreachIsFalse :
      uniprotAnnotationEstablishesAttributionBreach ≡ false
    kitzerowPriorityEvidenceCreatesProteinTruth : Bool
    kitzerowPriorityEvidenceCreatesProteinTruthIsFalse :
      kitzerowPriorityEvidenceCreatesProteinTruth ≡ false

canonicalKitzerowUniProtBoundary : KitzerowUniProtBoundary
canonicalKitzerowUniProtBoundary =
  kitzerowUniProtBoundary false refl false refl false refl false refl false refl

canonicalKitzerowUniProtCrossPollinationReceipt : Receipt.GenericReceipt
canonicalKitzerowUniProtCrossPollinationReceipt =
  Receipt.mkNonPromotingReceipt
    "Kitzerow / UniProt cross-pollination"
    "DASHI.Biology.KitzerowUniProtCrossPollinationExact"
    "QDPR BH4-regeneration claim -> Kitzerow bh4Availability target"
    "lets externally versioned protein/reaction evidence pay bounded atlas nodes while preserving the scientific-support/priority/contact/attribution product from PR #1159"
    "node support is not whole-model confirmation; UniProt cannot create Kitzerow priority/contact/attribution evidence; Kitzerow provenance cannot create protein truth"
    "agda -i . DASHI/Biology/KitzerowUniProtCrossPollinationExact.agda"
