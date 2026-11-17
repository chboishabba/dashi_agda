module DASHI.Interop.PNFSpectralFieldCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- PNF-as-spectral-field core surface.
--
-- This module introduces typed object vocabulary for a finite PNF spectral
-- field over the existing SensibLaw residual carrier.  It is deliberately a
-- checked object model only: references, fibres, support packets, braid paths,
-- and residual edges do not promote runtime text embeddings, vector proximity,
-- or candidate search results into semantic truth, support, or admissibility.

data PNFSpectralFieldStatus : Set where
  checkedCoreSurface_noRuntimePromotion :
    PNFSpectralFieldStatus

data PredicateAtomRef : Set where
  predicateAtomRef : Nat → PredicateAtomRef
  predicateAtomFallback : PredicateAtomRef

data PredicatePNFRef : Set where
  predicatePNFRef : Nat → PredicatePNFRef
  predicatePNFFallback : PredicatePNFRef

data FibreRef : Set where
  fibreRef : Nat → FibreRef
  fibreFallback : FibreRef

data ResidualEdgeRef : Set where
  residualEdgeRef : Nat → ResidualEdgeRef
  residualEdgeFallback : ResidualEdgeRef

data BraidPathRef : Set where
  braidPathRef : Nat → BraidPathRef
  braidPathFallback : BraidPathRef

data SupportPacketRef : Set where
  supportPacketRef : Nat → SupportPacketRef
  supportPacketFallback : SupportPacketRef

data CandidateRef : Set where
  candidateRef : Nat → CandidateRef
  candidateFallback : CandidateRef

data EvidenceBaseRef : Set where
  evidenceBaseRef : Nat → EvidenceBaseRef
  evidenceBaseFallback : EvidenceBaseRef

data TimeBaseRef : Set where
  timeBaseRef : Nat → TimeBaseRef
  timeBaseFallback : TimeBaseRef

record PredicateObjectRef : Set where
  constructor predicateObjectRef
  field
    atomRef : PredicateAtomRef
    pnfRef : PredicatePNFRef
    candidate : CandidateRef

open PredicateObjectRef public

canonicalPredicateObjectRef : PredicateObjectRef
canonicalPredicateObjectRef =
  predicateObjectRef
    predicateAtomFallback
    predicatePNFFallback
    candidateFallback

------------------------------------------------------------------------
-- Structural base and chamber projections over Residual.PredicatePNF.

record PNFStructuralBase : Set where
  constructor pnfStructuralBase
  field
    structuralSignature :
      Residual.StructuralSignature

    qualifier :
      Residual.QualifierState

    wrapper :
      Residual.WrapperState

open PNFStructuralBase public

record PNFEvidenceTimeBase : Set where
  constructor pnfEvidenceTimeBase
  field
    evidenceBase :
      EvidenceBaseRef

    evidenceParserProfile :
      String

    evidenceReducerProfile :
      String

    evidenceSourceSpan :
      String

    evidenceProvenance :
      String

    timeBase :
      TimeBaseRef

    timeBaseStatement :
      String

open PNFEvidenceTimeBase public

record PNFProductBase : Set where
  constructor pnfProductBase
  field
    structuralComponent :
      PNFStructuralBase

    evidenceComponent :
      PNFEvidenceTimeBase

open PNFProductBase public

record PNFCoordinateShape : Set where
  constructor pnfCoordinateShape
  field
    parserProfile : String
    reducerProfile : String
    sourceSpan : String
    provenance : String

open PNFCoordinateShape public

record PNFChamberProjection : Set where
  constructor pnfChamberProjection
  field
    chamberObject :
      PredicateObjectRef

    predicateText :
      String

    agent :
      Residual.TypedArg

    theme :
      Residual.TypedArg

    goal :
      Residual.TypedArg

    chamberBase :
      PNFStructuralBase

    chamberCoordinate :
      PNFCoordinateShape

open PNFChamberProjection public

pnfStructuralSignature :
  Residual.PredicatePNF →
  Residual.StructuralSignature
pnfStructuralSignature p =
  Residual.PredicatePNF.structuralSignature p

pnfQualifier :
  Residual.PredicatePNF →
  Residual.QualifierState
pnfQualifier p =
  Residual.PredicatePNF.qualifier p

pnfWrapper :
  Residual.PredicatePNF →
  Residual.WrapperState
pnfWrapper p =
  Residual.PredicatePNF.wrapper p

pnfStructuralBaseOf :
  Residual.PredicatePNF →
  PNFStructuralBase
pnfStructuralBaseOf p =
  pnfStructuralBase
    (pnfStructuralSignature p)
    (pnfQualifier p)
    (pnfWrapper p)

pnfCoordinateOfReceipt :
  Residual.PNFEmissionReceipt →
  PNFCoordinateShape
pnfCoordinateOfReceipt r =
  pnfCoordinateShape
    (Residual.PNFEmissionReceipt.parserProfile r)
    (Residual.PNFEmissionReceipt.reducerProfile r)
    (Residual.PNFEmissionReceipt.sourceSpan r)
    (Residual.PredicatePNF.provenance
      (Residual.PNFEmissionReceipt.emittedAtom r))

pnfReceiptOnlyTimeBaseStatement :
  String
pnfReceiptOnlyTimeBaseStatement =
  "PNF spectral field time base is an explicit receipt coordinate, not a runtime clock, ordering claim, or freshness proof."

pnfEvidenceTimeBaseOfReceipt :
  Residual.PNFEmissionReceipt →
  PNFEvidenceTimeBase
pnfEvidenceTimeBaseOfReceipt r =
  pnfEvidenceTimeBase
    evidenceBaseFallback
    (Residual.PNFEmissionReceipt.parserProfile r)
    (Residual.PNFEmissionReceipt.reducerProfile r)
    (Residual.PNFEmissionReceipt.sourceSpan r)
    (Residual.PredicatePNF.provenance
      (Residual.PNFEmissionReceipt.emittedAtom r))
    timeBaseFallback
    pnfReceiptOnlyTimeBaseStatement

pnfProductBaseOfReceipt :
  Residual.PNFEmissionReceipt →
  PNFProductBase
pnfProductBaseOfReceipt r =
  pnfProductBase
    (pnfStructuralBaseOf
      (Residual.PNFEmissionReceipt.emittedAtom r))
    (pnfEvidenceTimeBaseOfReceipt r)

pnfProductBaseStructuralProjectionIsCanonical :
  ∀ r →
  PNFProductBase.structuralComponent
    (pnfProductBaseOfReceipt r)
  ≡
  pnfStructuralBaseOf
    (Residual.PNFEmissionReceipt.emittedAtom r)
pnfProductBaseStructuralProjectionIsCanonical r =
  refl

pnfProductBaseEvidenceProjectionIsCanonical :
  ∀ r →
  PNFProductBase.evidenceComponent
    (pnfProductBaseOfReceipt r)
  ≡
  pnfEvidenceTimeBaseOfReceipt r
pnfProductBaseEvidenceProjectionIsCanonical r =
  refl

pnfChamberProjectionOfReceipt :
  PredicateObjectRef →
  Residual.PNFEmissionReceipt →
  PNFChamberProjection
pnfChamberProjectionOfReceipt obj r =
  pnfChamberProjection
    obj
    (Residual.PredicatePNF.predicate atom)
    (Residual.PredicatePNF.agent atom)
    (Residual.PredicatePNF.theme atom)
    (Residual.PredicatePNF.goal atom)
    (pnfStructuralBaseOf atom)
    (pnfCoordinateOfReceipt r)
  where
    atom : Residual.PredicatePNF
    atom = Residual.PNFEmissionReceipt.emittedAtom r

pnfChamberProjectionBaseIsCanonical :
  ∀ obj r →
  PNFChamberProjection.chamberBase
    (pnfChamberProjectionOfReceipt obj r)
  ≡
  pnfStructuralBaseOf
    (Residual.PNFEmissionReceipt.emittedAtom r)
pnfChamberProjectionBaseIsCanonical obj r =
  refl

pnfChamberProjectionCoordinateIsCanonical :
  ∀ obj r →
  PNFChamberProjection.chamberCoordinate
    (pnfChamberProjectionOfReceipt obj r)
  ≡
  pnfCoordinateOfReceipt r
pnfChamberProjectionCoordinateIsCanonical obj r =
  refl

------------------------------------------------------------------------
-- Fibres, field sections, residual edges, braid paths, and support packets.

record ObjectInFibre : Set where
  constructor objectInFibre
  field
    fibreObject :
      PredicateObjectRef

    objectFibre :
      FibreRef

    objectChamber :
      PNFChamberProjection

    fibreSignature :
      Residual.StructuralSignature

    chamberSignature :
      PNFStructuralBase.structuralSignature
        (PNFChamberProjection.chamberBase objectChamber)
      ≡
      fibreSignature

open ObjectInFibre public

objectInFibreOfReceipt :
  PredicateObjectRef →
  FibreRef →
  Residual.PNFEmissionReceipt →
  ObjectInFibre
objectInFibreOfReceipt obj fib r =
  objectInFibre
    obj
    fib
    chamber
    (PNFStructuralBase.structuralSignature
      (PNFChamberProjection.chamberBase chamber))
    refl
  where
    chamber : PNFChamberProjection
    chamber = pnfChamberProjectionOfReceipt obj r

record FibreNeighborhood : Set where
  constructor fibreNeighborhood
  field
    centre :
      FibreRef

    sameSignatureObjects :
      List PredicateObjectRef

    residualEdges :
      List ResidualEdgeRef

    braidPaths :
      List BraidPathRef

open FibreNeighborhood public

record ResidualFieldEdge : Set where
  constructor residualFieldEdge
  field
    edge :
      ResidualEdgeRef

    edgeSource :
      PredicateObjectRef

    edgeTarget :
      PredicateObjectRef

    residual :
      Residual.ResidualLevel

    residualIsComputedInsideTypedSurface :
      Bool

open ResidualFieldEdge public

canonicalResidualFieldEdge :
  ResidualFieldEdge
canonicalResidualFieldEdge =
  residualFieldEdge
    residualEdgeFallback
    canonicalPredicateObjectRef
    canonicalPredicateObjectRef
    Residual.noTypedMeet
    false

record BraidPath : Set where
  constructor braidPath
  field
    path :
      BraidPathRef

    endpoints :
      ResidualFieldEdge

    intermediateObjects :
      List PredicateObjectRef

    pathResidual :
      Residual.SixResidualLevel

open BraidPath public

canonicalBraidPath :
  BraidPath
canonicalBraidPath =
  braidPath
    braidPathFallback
    canonicalResidualFieldEdge
    []
    Residual.noTypedMeet6

record SupportPacketMembers : Set where
  constructor supportPacketMembers
  field
    packet :
      SupportPacketRef

    supportFibre :
      FibreRef

    members :
      List PredicateObjectRef

    localEdges :
      List ResidualEdgeRef

    braidWitnesses :
      List BraidPathRef

open SupportPacketMembers public

record FieldSection : Set where
  constructor fieldSection
  field
    sectionRef :
      SupportPacketRef

    baseFibre :
      FibreRef

    sectionNeighborhood :
      FibreNeighborhood

    sectionObjects :
      List ObjectInFibre

    sectionSupport :
      SupportPacketMembers

open FieldSection public

record ProductFieldSection : Set where
  constructor productFieldSection
  field
    productSectionRef :
      SupportPacketRef

    productBase :
      PNFProductBase

    structuralSection :
      FieldSection

    structuralSectionBase :
      FibreRef

    evidenceSectionBase :
      EvidenceBaseRef

    timeSectionBase :
      TimeBaseRef

open ProductFieldSection public

canonicalFibreNeighborhood :
  FibreNeighborhood
canonicalFibreNeighborhood =
  fibreNeighborhood
    fibreFallback
    (canonicalPredicateObjectRef ∷ [])
    (residualEdgeFallback ∷ [])
    (braidPathFallback ∷ [])

canonicalSupportPacketMembers :
  SupportPacketMembers
canonicalSupportPacketMembers =
  supportPacketMembers
    supportPacketFallback
    fibreFallback
    (canonicalPredicateObjectRef ∷ [])
    (residualEdgeFallback ∷ [])
    (braidPathFallback ∷ [])

canonicalFieldSection :
  FieldSection
canonicalFieldSection =
  fieldSection
    supportPacketFallback
    fibreFallback
    canonicalFibreNeighborhood
    []
    canonicalSupportPacketMembers

canonicalEvidenceTimeBase :
  PNFEvidenceTimeBase
canonicalEvidenceTimeBase =
  pnfEvidenceTimeBase
    evidenceBaseFallback
    ""
    ""
    ""
    ""
    timeBaseFallback
    pnfReceiptOnlyTimeBaseStatement

canonicalProductBase :
  PNFProductBase
canonicalProductBase =
  pnfProductBase
    (pnfStructuralBase
      Residual.sig-unclassified
      Residual.qualifierUnknown
      Residual.wrapperUnknown)
    canonicalEvidenceTimeBase

canonicalProductFieldSection :
  ProductFieldSection
canonicalProductFieldSection =
  productFieldSection
    supportPacketFallback
    canonicalProductBase
    canonicalFieldSection
    fibreFallback
    evidenceBaseFallback
    timeBaseFallback

------------------------------------------------------------------------
-- Authority boundary.

data PNFSpectralFieldPromotion : Set where

pnfSpectralFieldPromotionImpossible :
  PNFSpectralFieldPromotion →
  ⊥
pnfSpectralFieldPromotionImpossible ()

data PNFSpectralFieldComponent : Set where
  predicateAtomReferenceVocabulary :
    PNFSpectralFieldComponent

  predicatePNFReferenceVocabulary :
    PNFSpectralFieldComponent

  typedFibreAndResidualEdgeVocabulary :
    PNFSpectralFieldComponent

  braidPathAndSupportPacketVocabulary :
    PNFSpectralFieldComponent

  chamberProjectionOverResidualPNF :
    PNFSpectralFieldComponent

  evidenceProvenanceTimeBase :
    PNFSpectralFieldComponent

  productBaseOverStructuralEvidence :
    PNFSpectralFieldComponent

  canonicalProductProjectionReceipt :
    PNFSpectralFieldComponent

  explicitEmbeddingBoundary :
    PNFSpectralFieldComponent

  receiptOnlyNoRuntimePromotion :
    PNFSpectralFieldComponent

canonicalPNFSpectralFieldComponents :
  List PNFSpectralFieldComponent
canonicalPNFSpectralFieldComponents =
  predicateAtomReferenceVocabulary
  ∷ predicatePNFReferenceVocabulary
  ∷ typedFibreAndResidualEdgeVocabulary
  ∷ braidPathAndSupportPacketVocabulary
  ∷ chamberProjectionOverResidualPNF
  ∷ evidenceProvenanceTimeBase
  ∷ productBaseOverStructuralEvidence
  ∷ canonicalProductProjectionReceipt
  ∷ explicitEmbeddingBoundary
  ∷ receiptOnlyNoRuntimePromotion
  ∷ []

textEmbeddingImpliesTruth :
  Bool
textEmbeddingImpliesTruth =
  false

vectorProximityImpliesSupport :
  Bool
vectorProximityImpliesSupport =
  false

candidateMembershipImpliesAdmissibility :
  Bool
candidateMembershipImpliesAdmissibility =
  false

supportPacketImpliesTruth :
  Bool
supportPacketImpliesTruth =
  false

residualEdgeImpliesRuntimeEvidence :
  Bool
residualEdgeImpliesRuntimeEvidence =
  false

pnfSpectralFieldStatement :
  String
pnfSpectralFieldStatement =
  "PNFSpectralField is a checked typed object model over PredicatePNF structural base and chamber coordinates; refs, fibres, residual edges, braid paths, support packets, and candidates are non-promoting carriers."

pnfSpectralFieldBoundaryStatement :
  String
pnfSpectralFieldBoundaryStatement =
  "Text embedding and vector proximity do not imply truth, support, admissibility, runtime PNF emission, policy/legal/Wikidata authority, or semantic promotion; only explicit receipts may be consumed."

record PNFSpectralFieldReceipt : Set where
  field
    status :
      PNFSpectralFieldStatus

    statusIsCheckedNoRuntimePromotion :
      status ≡ checkedCoreSurface_noRuntimePromotion

    predicateObject :
      PredicateObjectRef

    predicateObjectIsCanonical :
      predicateObject ≡ canonicalPredicateObjectRef

    structuralBaseProjection :
      Residual.PredicatePNF →
      PNFStructuralBase

    structuralBaseProjectionIsCanonical :
      structuralBaseProjection ≡ pnfStructuralBaseOf

    coordinateProjection :
      Residual.PNFEmissionReceipt →
      PNFCoordinateShape

    coordinateProjectionIsCanonical :
      coordinateProjection ≡ pnfCoordinateOfReceipt

    evidenceTimeBaseProjection :
      Residual.PNFEmissionReceipt →
      PNFEvidenceTimeBase

    evidenceTimeBaseProjectionIsCanonical :
      evidenceTimeBaseProjection ≡ pnfEvidenceTimeBaseOfReceipt

    productBaseProjection :
      Residual.PNFEmissionReceipt →
      PNFProductBase

    productBaseProjectionIsCanonical :
      productBaseProjection ≡ pnfProductBaseOfReceipt

    chamberProjection :
      PredicateObjectRef →
      Residual.PNFEmissionReceipt →
      PNFChamberProjection

    chamberProjectionIsCanonical :
      chamberProjection ≡ pnfChamberProjectionOfReceipt

    receiptNeighborhood :
      FibreNeighborhood

    neighbourhoodIsCanonical :
      receiptNeighborhood ≡ canonicalFibreNeighborhood

    supportMembers :
      SupportPacketMembers

    supportMembersAreCanonical :
      supportMembers ≡ canonicalSupportPacketMembers

    section :
      FieldSection

    sectionIsCanonical :
      section ≡ canonicalFieldSection

    productSection :
      ProductFieldSection

    productSectionIsCanonical :
      productSection ≡ canonicalProductFieldSection

    components :
      List PNFSpectralFieldComponent

    componentsAreCanonical :
      components ≡ canonicalPNFSpectralFieldComponents

    statement :
      String

    statementIsCanonical :
      statement ≡ pnfSpectralFieldStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ pnfSpectralFieldBoundaryStatement

    textEmbeddingTruthPromotion :
      Bool

    textEmbeddingTruthPromotionIsFalse :
      textEmbeddingTruthPromotion ≡ false

    vectorProximitySupportPromotion :
      Bool

    vectorProximitySupportPromotionIsFalse :
      vectorProximitySupportPromotion ≡ false

    candidateAdmissibilityPromotion :
      Bool

    candidateAdmissibilityPromotionIsFalse :
      candidateAdmissibilityPromotion ≡ false

    supportPacketTruthPromotion :
      Bool

    supportPacketTruthPromotionIsFalse :
      supportPacketTruthPromotion ≡ false

    residualEdgeRuntimeEvidencePromotion :
      Bool

    residualEdgeRuntimeEvidencePromotionIsFalse :
      residualEdgeRuntimeEvidencePromotion ≡ false

    semanticTruthPromotion :
      Bool

    semanticTruthPromotionIsFalse :
      semanticTruthPromotion ≡ false

    policyLegalWikidataAuthority :
      Bool

    policyLegalWikidataAuthorityIsFalse :
      policyLegalWikidataAuthority ≡ false

    promotionFlags :
      List PNFSpectralFieldPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open PNFSpectralFieldReceipt public

canonicalPNFSpectralFieldReceipt :
  PNFSpectralFieldReceipt
canonicalPNFSpectralFieldReceipt =
  record
    { status =
        checkedCoreSurface_noRuntimePromotion
    ; statusIsCheckedNoRuntimePromotion =
        refl
    ; predicateObject =
        canonicalPredicateObjectRef
    ; predicateObjectIsCanonical =
        refl
    ; structuralBaseProjection =
        pnfStructuralBaseOf
    ; structuralBaseProjectionIsCanonical =
        refl
    ; coordinateProjection =
        pnfCoordinateOfReceipt
    ; coordinateProjectionIsCanonical =
        refl
    ; evidenceTimeBaseProjection =
        pnfEvidenceTimeBaseOfReceipt
    ; evidenceTimeBaseProjectionIsCanonical =
        refl
    ; productBaseProjection =
        pnfProductBaseOfReceipt
    ; productBaseProjectionIsCanonical =
        refl
    ; chamberProjection =
        pnfChamberProjectionOfReceipt
    ; chamberProjectionIsCanonical =
        refl
    ; receiptNeighborhood =
        canonicalFibreNeighborhood
    ; neighbourhoodIsCanonical =
        refl
    ; supportMembers =
        canonicalSupportPacketMembers
    ; supportMembersAreCanonical =
        refl
    ; section =
        canonicalFieldSection
    ; sectionIsCanonical =
        refl
    ; productSection =
        canonicalProductFieldSection
    ; productSectionIsCanonical =
        refl
    ; components =
        canonicalPNFSpectralFieldComponents
    ; componentsAreCanonical =
        refl
    ; statement =
        pnfSpectralFieldStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        pnfSpectralFieldBoundaryStatement
    ; boundaryIsCanonical =
        refl
    ; textEmbeddingTruthPromotion =
        textEmbeddingImpliesTruth
    ; textEmbeddingTruthPromotionIsFalse =
        refl
    ; vectorProximitySupportPromotion =
        vectorProximityImpliesSupport
    ; vectorProximitySupportPromotionIsFalse =
        refl
    ; candidateAdmissibilityPromotion =
        candidateMembershipImpliesAdmissibility
    ; candidateAdmissibilityPromotionIsFalse =
        refl
    ; supportPacketTruthPromotion =
        supportPacketImpliesTruth
    ; supportPacketTruthPromotionIsFalse =
        refl
    ; residualEdgeRuntimeEvidencePromotion =
        residualEdgeImpliesRuntimeEvidence
    ; residualEdgeRuntimeEvidencePromotionIsFalse =
        refl
    ; semanticTruthPromotion =
        false
    ; semanticTruthPromotionIsFalse =
        refl
    ; policyLegalWikidataAuthority =
        false
    ; policyLegalWikidataAuthorityIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }
