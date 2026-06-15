module DASHI.Interop.PNFSpectralFieldGraph where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.PNFResidualSpectralSeverityReceipt as SpectralSeverity
import DASHI.Interop.SensibLawResidualLattice as Residual
import UFTC_Lattice as UFTC

------------------------------------------------------------------------
-- Weighted residual graph surface for the PNF spectral field.
--
-- This module only exposes a finite symbolic addressing operator.  Edges are
-- typed by structural evidence constructors and residual classes; weights are
-- computed from those constructors and from the finite residual severity
-- lattice, not from free text labels.

data PNFGraphVertex : Set where
  pnfGraphVertex : Nat → PNFGraphVertex

record PNFGraphNode : Set where
  constructor pnfGraphNode
  field
    vertex : PNFGraphVertex
    receipt : Residual.PNFEmissionReceipt

open PNFGraphNode public

data PNFGraphEdgeKind : Set where
  sameFibreEdge : PNFGraphEdgeKind
  exactResidualEdge : PNFGraphEdgeKind
  partialResidualEdge : PNFGraphEdgeKind
  compatibleJoinEdge : PNFGraphEdgeKind
  compatibleMeetEdge : PNFGraphEdgeKind
  sharedProvenanceEdge : PNFGraphEdgeKind
  sharedSourceEdge : PNFGraphEdgeKind
  sharedTimeEdge : PNFGraphEdgeKind
  temporalContinuationEdge : PNFGraphEdgeKind
  contradictionEdge : PNFGraphEdgeKind

data PNFGraphWeightClass : Set where
  fibreWeight : PNFGraphWeightClass
  exactResidualWeight : PNFGraphWeightClass
  partialResidualWeight : PNFGraphWeightClass
  compatibleJoinWeight : PNFGraphWeightClass
  compatibleMeetWeight : PNFGraphWeightClass
  sharedProvenanceWeight : PNFGraphWeightClass
  sharedSourceWeight : PNFGraphWeightClass
  sharedTimeWeight : PNFGraphWeightClass
  temporalContinuationWeight : PNFGraphWeightClass
  contradictionSignedWeight : PNFGraphWeightClass

edgeKindWeightClass : PNFGraphEdgeKind → PNFGraphWeightClass
edgeKindWeightClass sameFibreEdge = fibreWeight
edgeKindWeightClass exactResidualEdge = exactResidualWeight
edgeKindWeightClass partialResidualEdge = partialResidualWeight
edgeKindWeightClass compatibleJoinEdge = compatibleJoinWeight
edgeKindWeightClass compatibleMeetEdge = compatibleMeetWeight
edgeKindWeightClass sharedProvenanceEdge = sharedProvenanceWeight
edgeKindWeightClass sharedSourceEdge = sharedSourceWeight
edgeKindWeightClass sharedTimeEdge = sharedTimeWeight
edgeKindWeightClass temporalContinuationEdge = temporalContinuationWeight
edgeKindWeightClass contradictionEdge = contradictionSignedWeight

data ResidualWeightTag : Set where
  exactResidualSeverityWeight : ResidualWeightTag
  partialResidualSeverityWeight : ResidualWeightTag
  noTypedMeetResidualSeverityWeight : ResidualWeightTag
  contradictionResidualSignedSeverityWeight : ResidualWeightTag

residualWeightTag : Residual.ResidualLevel → ResidualWeightTag
residualWeightTag Residual.exact = exactResidualSeverityWeight
residualWeightTag Residual.partial = partialResidualSeverityWeight
residualWeightTag Residual.noTypedMeet = noTypedMeetResidualSeverityWeight
residualWeightTag Residual.contradiction =
  contradictionResidualSignedSeverityWeight

residualWeightSeverity : Residual.ResidualLevel → UFTC.Severity
residualWeightSeverity =
  Residual.residualSeverity

exactResidualWeightTagIsExact :
  residualWeightTag Residual.exact ≡ exactResidualSeverityWeight
exactResidualWeightTagIsExact =
  refl

partialResidualWeightTagIsPartial :
  residualWeightTag Residual.partial ≡ partialResidualSeverityWeight
partialResidualWeightTagIsPartial =
  refl

noTypedMeetResidualWeightTagIsNoTypedMeet :
  residualWeightTag Residual.noTypedMeet ≡ noTypedMeetResidualSeverityWeight
noTypedMeetResidualWeightTagIsNoTypedMeet =
  refl

contradictionResidualWeightTagIsSigned :
  residualWeightTag Residual.contradiction
  ≡
  contradictionResidualSignedSeverityWeight
contradictionResidualWeightTagIsSigned =
  refl

exactResidualWeightSeverityIsZero :
  residualWeightSeverity Residual.exact ≡ 0
exactResidualWeightSeverityIsZero =
  SpectralSeverity.exactSeverityIsZero

partialResidualWeightSeverityIsOne :
  residualWeightSeverity Residual.partial ≡ 1
partialResidualWeightSeverityIsOne =
  SpectralSeverity.partialSeverityIsOne

noTypedMeetResidualWeightSeverityIsThree :
  residualWeightSeverity Residual.noTypedMeet ≡ 3
noTypedMeetResidualWeightSeverityIsThree =
  SpectralSeverity.noTypedMeetSeverityIsThree

contradictionResidualWeightSeverityIsNine :
  residualWeightSeverity Residual.contradiction ≡ 9
contradictionResidualWeightSeverityIsNine =
  SpectralSeverity.contradictionSeverityIsNine

data WeightSign : Set where
  positiveWeight : WeightSign
  negativeResidualWeight : WeightSign

record SignedResidualWeight : Set where
  constructor signedResidualWeight
  field
    sign : WeightSign
    magnitude : UFTC.Severity
    residualTag : ResidualWeightTag

open SignedResidualWeight public

residualSignedWeight : Residual.ResidualLevel → SignedResidualWeight
residualSignedWeight Residual.exact =
  signedResidualWeight
    positiveWeight
    (Residual.residualSeverity Residual.exact)
    exactResidualSeverityWeight
residualSignedWeight Residual.partial =
  signedResidualWeight
    positiveWeight
    (Residual.residualSeverity Residual.partial)
    partialResidualSeverityWeight
residualSignedWeight Residual.noTypedMeet =
  signedResidualWeight
    positiveWeight
    (Residual.residualSeverity Residual.noTypedMeet)
    noTypedMeetResidualSeverityWeight
residualSignedWeight Residual.contradiction =
  signedResidualWeight
    negativeResidualWeight
    (Residual.residualSeverity Residual.contradiction)
    contradictionResidualSignedSeverityWeight

contradictionSignedWeightIsNegative :
  sign (residualSignedWeight Residual.contradiction)
  ≡
  negativeResidualWeight
contradictionSignedWeightIsNegative =
  refl

data PNFGraphEdgeEvidence : PNFGraphEdgeKind → Set where
  sameFibreEvidence :
    Residual.StructuralSignature →
    PNFGraphEdgeEvidence sameFibreEdge

  exactResidualEvidence :
    PNFGraphEdgeEvidence exactResidualEdge

  partialResidualEvidence :
    PNFGraphEdgeEvidence partialResidualEdge

  compatibleJoinEvidence :
    Residual.ResidualLevel →
    Residual.ResidualLevel →
    PNFGraphEdgeEvidence compatibleJoinEdge

  compatibleMeetEvidence :
    Residual.ResidualLevel →
    Residual.ResidualLevel →
    PNFGraphEdgeEvidence compatibleMeetEdge

  sharedProvenanceEvidence :
    String →
    PNFGraphEdgeEvidence sharedProvenanceEdge

  sharedSourceEvidence :
    String →
    PNFGraphEdgeEvidence sharedSourceEdge

  sharedTimeEvidence :
    String →
    PNFGraphEdgeEvidence sharedTimeEdge

  temporalContinuationEvidence :
    String →
    String →
    PNFGraphEdgeEvidence temporalContinuationEdge

  contradictionEvidence :
    PNFGraphEdgeEvidence contradictionEdge

record PNFGraphEdge : Set where
  constructor pnfGraphEdge
  field
    left : PNFGraphVertex
    right : PNFGraphVertex
    kind : PNFGraphEdgeKind
    evidence : PNFGraphEdgeEvidence kind
    weightClass : PNFGraphWeightClass
    weightClassIsStructural : weightClass ≡ edgeKindWeightClass kind

open PNFGraphEdge public

mkPNFGraphEdge :
  ∀ {kind} →
  PNFGraphVertex →
  PNFGraphVertex →
  PNFGraphEdgeEvidence kind →
  PNFGraphEdge
mkPNFGraphEdge {kind} left right evidence =
  pnfGraphEdge
    left
    right
    kind
    evidence
    (edgeKindWeightClass kind)
    refl

record WeightedPNFGraph : Set where
  constructor weightedPNFGraph
  field
    vertices : List PNFGraphVertex
    edges : List PNFGraphEdge
    edgeWeight : PNFGraphEdge → UFTC.Severity
    edgeWeightClass : PNFGraphEdge → PNFGraphWeightClass
    edgeWeightClassIsStructural :
      ∀ e → edgeWeightClass e ≡ edgeKindWeightClass (kind e)

open WeightedPNFGraph public

record SignedPNFGraph : Set where
  constructor signedPNFGraph
  field
    weightedGraph : WeightedPNFGraph
    signedEdgeWeight : PNFGraphEdge → SignedResidualWeight
    contradictionEdgesAreNegative :
      ∀ e →
      kind e ≡ contradictionEdge →
      sign (signedEdgeWeight e) ≡ negativeResidualWeight

open SignedPNFGraph public

record DiagonalDegreeOperator : Set where
  constructor diagonalDegreeOperator
  field
    degreeGraph : WeightedPNFGraph
    diagonalDegree : PNFGraphVertex → UFTC.Severity
    diagonalDegreeStatement : String

open DiagonalDegreeOperator public

record GraphLaplacianOperator : Set where
  constructor graphLaplacianOperator
  field
    laplacianGraph : WeightedPNFGraph
    degree : DiagonalDegreeOperator
    adjacencyWeight : PNFGraphVertex → PNFGraphVertex → UFTC.Severity
    laplacianEntry : PNFGraphVertex → PNFGraphVertex → UFTC.Severity
    laplacianStatement : String

open GraphLaplacianOperator public

record SignedResidualLaplacianOperator : Set where
  constructor signedResidualLaplacianOperator
  field
    signedGraph : SignedPNFGraph
    positivePart : GraphLaplacianOperator
    negativeResidualPart :
      PNFGraphVertex → PNFGraphVertex → SignedResidualWeight
    signedLaplacianEntry :
      PNFGraphVertex → PNFGraphVertex → SignedResidualWeight
    contradictionPartRemainsSigned :
      ∀ v w →
      sign (signedLaplacianEntry v w) ≡ negativeResidualWeight →
      Bool
    signedLaplacianStatement : String

open SignedResidualLaplacianOperator public

record SpectralCoordinateRow : Set where
  constructor spectralCoordinateRow
  field
    coordinateVertex : PNFGraphVertex
    exactCoordinate : UFTC.Severity
    partialCoordinate : UFTC.Severity
    noTypedMeetCoordinate : UFTC.Severity
    contradictionCoordinate : SignedResidualWeight
    rowStatement : String

open SpectralCoordinateRow public

canonicalSpectralCoordinateRow :
  PNFGraphVertex →
  SpectralCoordinateRow
canonicalSpectralCoordinateRow v =
  spectralCoordinateRow
    v
    (Residual.residualSeverity Residual.exact)
    (Residual.residualSeverity Residual.partial)
    (Residual.residualSeverity Residual.noTypedMeet)
    (residualSignedWeight Residual.contradiction)
    "Finite PNF residual coordinate row: exact, partial, noTypedMeet, and signed contradiction coordinates are addressed as finite residual severity slots."

canonicalSpectralCoordinateRowExactIsZero :
  ∀ v → exactCoordinate (canonicalSpectralCoordinateRow v) ≡ 0
canonicalSpectralCoordinateRowExactIsZero v =
  refl

canonicalSpectralCoordinateRowContradictionIsSigned :
  ∀ v →
  sign (contradictionCoordinate (canonicalSpectralCoordinateRow v))
  ≡
  negativeResidualWeight
canonicalSpectralCoordinateRowContradictionIsSigned v =
  refl

------------------------------------------------------------------------
-- Canonical finite receipt and promotion boundary.

data PNFSpectralFieldGraphStatus : Set where
  finiteAddressingProposalOperator_noSemanticPromotion :
    PNFSpectralFieldGraphStatus

data PNFSpectralFieldGraphComponent : Set where
  typedResidualEdgeKindsComponent : PNFSpectralFieldGraphComponent
  structuralWeightClassesComponent : PNFSpectralFieldGraphComponent
  signedContradictionComponent : PNFSpectralFieldGraphComponent
  diagonalDegreeComponent : PNFSpectralFieldGraphComponent
  graphLaplacianComponent : PNFSpectralFieldGraphComponent
  signedResidualLaplacianComponent : PNFSpectralFieldGraphComponent
  finiteSpectralCoordinateRowComponent : PNFSpectralFieldGraphComponent
  finiteReceiptBoundaryComponent : PNFSpectralFieldGraphComponent

canonicalPNFSpectralFieldGraphComponents :
  List PNFSpectralFieldGraphComponent
canonicalPNFSpectralFieldGraphComponents =
  typedResidualEdgeKindsComponent
  ∷ structuralWeightClassesComponent
  ∷ signedContradictionComponent
  ∷ diagonalDegreeComponent
  ∷ graphLaplacianComponent
  ∷ signedResidualLaplacianComponent
  ∷ finiteSpectralCoordinateRowComponent
  ∷ finiteReceiptBoundaryComponent
  ∷ []

data PNFSpectralFieldGraphPromotion : Set where

pnfSpectralFieldGraphPromotionImpossible :
  PNFSpectralFieldGraphPromotion →
  ⊥
pnfSpectralFieldGraphPromotionImpossible ()

pnfSpectralFieldGraphStatement : String
pnfSpectralFieldGraphStatement =
  "The weighted residual graph is a finite symbolic addressing surface over PNF receipts. Edge kinds are typed structural constructors; residual weights reuse the finite residual severity lattice; contradiction is kept as a signed residual component."

pnfSpectralFieldGraphBoundaryStatement : String
pnfSpectralFieldGraphBoundaryStatement =
  "This receipt is only an addressing/proposal operator for finite PNF spectral field rows. It does not assert semantic truth, admissibility, runtime evidence, legal/policy authority, or any continuum spectral theorem."

record PNFSpectralFieldGraphReceipt : Set where
  field
    status :
      PNFSpectralFieldGraphStatus

    statusIsFiniteAddressingProposal :
      status
      ≡
      finiteAddressingProposalOperator_noSemanticPromotion

    severityReceipt :
      SpectralSeverity.PNFResidualSpectralSeverityReceipt

    severityReceiptIsCanonical :
      severityReceipt
      ≡
      SpectralSeverity.canonicalPNFResidualSpectralSeverityReceipt

    components :
      List PNFSpectralFieldGraphComponent

    componentsAreCanonical :
      components ≡ canonicalPNFSpectralFieldGraphComponents

    exactWeightTag :
      residualWeightTag Residual.exact
      ≡
      exactResidualSeverityWeight

    partialWeightTag :
      residualWeightTag Residual.partial
      ≡
      partialResidualSeverityWeight

    noTypedMeetWeightTag :
      residualWeightTag Residual.noTypedMeet
      ≡
      noTypedMeetResidualSeverityWeight

    contradictionWeightTag :
      residualWeightTag Residual.contradiction
      ≡
      contradictionResidualSignedSeverityWeight

    exactWeightSeverity :
      residualWeightSeverity Residual.exact ≡ 0

    partialWeightSeverity :
      residualWeightSeverity Residual.partial ≡ 1

    noTypedMeetWeightSeverity :
      residualWeightSeverity Residual.noTypedMeet ≡ 3

    contradictionWeightSeverity :
      residualWeightSeverity Residual.contradiction ≡ 9

    contradictionWeightSign :
      sign (residualSignedWeight Residual.contradiction)
      ≡
      negativeResidualWeight

    statement :
      String

    statementIsCanonical :
      statement ≡ pnfSpectralFieldGraphStatement

    addressingProposalOperator :
      Bool

    addressingProposalOperatorIsTrue :
      addressingProposalOperator ≡ true

    semanticTruthPromotion :
      Bool

    semanticTruthPromotionIsFalse :
      semanticTruthPromotion ≡ false

    admissibilityPromotion :
      Bool

    admissibilityPromotionIsFalse :
      admissibilityPromotion ≡ false

    runtimeEvidencePromotion :
      Bool

    runtimeEvidencePromotionIsFalse :
      runtimeEvidencePromotion ≡ false

    continuumSpectralPromotion :
      Bool

    continuumSpectralPromotionIsFalse :
      continuumSpectralPromotion ≡ false

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ pnfSpectralFieldGraphBoundaryStatement

    promotionFlags :
      List PNFSpectralFieldGraphPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open PNFSpectralFieldGraphReceipt public

canonicalPNFSpectralFieldGraphReceipt :
  PNFSpectralFieldGraphReceipt
canonicalPNFSpectralFieldGraphReceipt =
  record
    { status =
        finiteAddressingProposalOperator_noSemanticPromotion
    ; statusIsFiniteAddressingProposal =
        refl
    ; severityReceipt =
        SpectralSeverity.canonicalPNFResidualSpectralSeverityReceipt
    ; severityReceiptIsCanonical =
        refl
    ; components =
        canonicalPNFSpectralFieldGraphComponents
    ; componentsAreCanonical =
        refl
    ; exactWeightTag =
        refl
    ; partialWeightTag =
        refl
    ; noTypedMeetWeightTag =
        refl
    ; contradictionWeightTag =
        refl
    ; exactWeightSeverity =
        exactResidualWeightSeverityIsZero
    ; partialWeightSeverity =
        partialResidualWeightSeverityIsOne
    ; noTypedMeetWeightSeverity =
        noTypedMeetResidualWeightSeverityIsThree
    ; contradictionWeightSeverity =
        contradictionResidualWeightSeverityIsNine
    ; contradictionWeightSign =
        refl
    ; statement =
        pnfSpectralFieldGraphStatement
    ; statementIsCanonical =
        refl
    ; addressingProposalOperator =
        true
    ; addressingProposalOperatorIsTrue =
        refl
    ; semanticTruthPromotion =
        false
    ; semanticTruthPromotionIsFalse =
        refl
    ; admissibilityPromotion =
        false
    ; admissibilityPromotionIsFalse =
        refl
    ; runtimeEvidencePromotion =
        false
    ; runtimeEvidencePromotionIsFalse =
        refl
    ; continuumSpectralPromotion =
        false
    ; continuumSpectralPromotionIsFalse =
        refl
    ; boundary =
        pnfSpectralFieldGraphBoundaryStatement
    ; boundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

pnfSpectralFieldGraphNoSemanticTruthPromotion :
  semanticTruthPromotion canonicalPNFSpectralFieldGraphReceipt ≡ false
pnfSpectralFieldGraphNoSemanticTruthPromotion =
  refl

pnfSpectralFieldGraphNoAdmissibilityPromotion :
  admissibilityPromotion canonicalPNFSpectralFieldGraphReceipt ≡ false
pnfSpectralFieldGraphNoAdmissibilityPromotion =
  refl

pnfSpectralFieldGraphNoContinuumPromotion :
  continuumSpectralPromotion canonicalPNFSpectralFieldGraphReceipt ≡ false
pnfSpectralFieldGraphNoContinuumPromotion =
  refl
