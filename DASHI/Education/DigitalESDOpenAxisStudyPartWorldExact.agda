module DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact where

------------------------------------------------------------------------
-- SOURCE-GOVERNED N-AXIS STUDY-PART / WORLD ADMISSION CUT
--
-- Reuses canonical owners; it is NOT another source, PNF or hypergraph
-- ontology.  Original Digital-ESD source and paper claims remain attributed
-- to their authors; this is a DASHI methodological interface.
--
-- In particular, 3/9/27/369 are optional chart carriers, never bounds on
-- the set of research axes or the arity of an interaction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as SLR
import DASHI.Education.DigitalESDSourceAuditHyperfabricExact as Audit
import DASHI.Education.DigitalESDSourceAuditAdmissionExact as Admission
import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact as Canonical
import DASHI.Core.IntersectionalNonFactorability as Factor
import DASHI.Reasoning.TypedHyperfabricCore as Hyper
import DASHI.Algebra.BalancedTernary as Balanced

-- The finite set of currently DECLARED axes can have arbitrary cardinality.
-- Extension must be explicit. Exhaustiveness makes silently omitted axis
-- constructors and study parts impossible for an admitted world scope.
record StudyWorldScope : Set₁ where
  constructor study-world-scope
  field
    Study : Set
    Part : Study → Set
    Axis : Set

    studySource : Study → Attr.AttributedSource
    studyReference : Study → String
    partReference : (study : Study) → Part study → String
    axisReference : Axis → String

    studies : List Study
    studyIsListed : (study : Study) → study ∈ studies

    parts : (study : Study) → List (Part study)
    partIsListed : (study : Study) (part : Part study) →
      part ∈ parts study

    axes : List Axis
    axisIsListed : (axis : Axis) → axis ∈ axes

    -- Application-owned evidence relevance, not a default 'true' flag.
    -- A reviewer must prove that this exact observation bears on this
    -- particular part/axis in this source, not merely on the paper title.
    EvidenceBearsOn :
      (study : Study) → Part study → Axis →
      SLR.ReviewedSLRAuditObservation (studySource study) → Set

open StudyWorldScope public

record StudyPart (scope : StudyWorldScope) : Set where
  constructor study-part
  field
    study : Study scope
    part : Part scope study

open StudyPart public

-- Exact SLR -> canonical evidence -> same-source admitted audit join.
-- Source identity, observed packet membership, original full-text revision
-- and exact source-audit observation membership are independent obligations.
-- Unlike a label or a boolean, this cannot be built from a bare registry row.
record ReviewedPartAxisEvidence
  (scope : StudyWorldScope)
  (s : Study scope)
  (p : Part scope s)
  (a : Axis scope) : Set₁ where
  constructor reviewed-part-axis-evidence
  field
    packet : SLR.SLRSourceReviewPacket (studySource scope s)
    reviewed : SLR.ReviewedSLRAuditObservation (studySource scope s)
    reviewedInPacket :
      reviewed ∈ SLR.SLRSourceReviewPacket.reviewedObservations packet

    packetAnalysisHasSameFullText :
      SLR.SLRSourceReviewPacket.fullText packet ≡
      SLR.SLRSourceUnitAnalysisReceipt.fullText
        (SLR.SLRSourceReviewPacket.analysis packet)

    canonicalObservation : Canonical.EvidenceObservation
    canonicalObservationIsReviewed :
      canonicalObservation ≡
      SLR.SLRCandidateAuditObservation.canonicalEvidenceObservation
        (SLR.SLRObservationReviewReceipt.candidate
          (SLR.ReviewedSLRAuditObservation.reviewReceipt reviewed))

    canonicalRevisionIsFullText :
      Canonical.EvidenceObservation.observationSourceRevisionRef
        canonicalObservation ≡
      SLR.FullTextArtifactReceipt.fullTextRevisionReference
        (SLR.SLRSourceReviewPacket.fullText packet)

    canonicalSpanHasSameRevision :
      Canonical.ObservationRevisionWeld canonicalObservation

    admitted : Admission.SourceAuditAdmission (studySource scope s)
    admittedObservation :
      Audit.SameSourceObservation (studySource scope s)
    admittedObservationIsReviewed :
      Audit.SameSourceObservation.observation admittedObservation ≡
      SLR.ReviewedSLRAuditObservation.reviewedObservation reviewed
    admittedObservationInFabric :
      admittedObservation ∈
      Audit.SourceAuditHyperfabric.observations
        (Admission.SourceAuditAdmission.hyperfabric admitted)

    relevantToThisStudyPartAndAxis :
      EvidenceBearsOn scope s p a reviewed

open ReviewedPartAxisEvidence public

-- A source-dependent axis verdict. Direct evidence has full review/revision
-- obligations. Other cases remain explicit and cannot masquerade as direct
-- evidence. Unmeasured, inaccessible and not-applicable remain distinct.
data PartAxisAccounting
  (scope : StudyWorldScope)
  (s : Study scope)
  (p : Part scope s)
  (a : Axis scope) : Set₁ where
  directReviewed :
    ReviewedPartAxisEvidence scope s p a →
    PartAxisAccounting scope s p a
  -- Author-reported content seen in an article or abstract, still awaiting
  -- the exact SLR full-text, span, reviewer and audit membership receipts.
  -- This is *not* absent evidence and is *not* directReviewed evidence.
  sourceReportedPendingReview :
    (sourceSectionRef reportedObservationRef reviewDebt : String) →
    PartAxisAccounting scope s p a
  inferredUnderConditions :
    (premiseReference conditionReference limitation : String) →
    PartAxisAccounting scope s p a
  contestedBySources :
    (positionReference counterpositionReference disputeReference : String) →
    PartAxisAccounting scope s p a
  -- Not yet analysed is not "unmeasured". This state keeps candidate
  -- source decompositions structurally total without pretending review.
  notYetAssessed :
    (reviewWorkReference : String) →
    PartAxisAccounting scope s p a
  unmeasuredForQuestion :
    (questionReference missingEvidenceReference : String) →
    PartAxisAccounting scope s p a
  sourceInaccessible :
    (sourceAccessReference accessConstraint : String) →
    PartAxisAccounting scope s p a
  justifiedInapplicability :
    (questionReference justificationReference : String) →
    PartAxisAccounting scope s p a

-- Totality, rather than an optional list of selected studies or a fixed
-- source-level ten-axis scorecard, is the admission obligation. Its value
-- can be an explicitly unresolved/missing/not-applicable case.
record AccountedStudyWorld (scope : StudyWorldScope) : Set₂ where
  constructor accounted-study-world
  field
    accounting :
      (s : Study scope) (p : Part scope s) (a : Axis scope) →
      PartAxisAccounting scope s p a

open AccountedStudyWorld public

-- Candidate study-part relationships have no fixed number of participants,
-- no fixed axis count and no requirement to collapse into a binary score.
-- A signed trit is a *qualified view*, not a statement that an
-- epistemically unknown / N/A / contested state all means zero.
data RelationValue (Scalar : Set) : Set where
  scalarValue : Scalar → RelationValue Scalar
  signedTernaryView : Balanced.Trit → RelationValue Scalar

record HigherOrderStudyRelation
  (scope : StudyWorldScope)
  (Scalar : Set) : Set₁ where
  constructor higher-order-study-relation
  field
    participatingStudyParts : List (StudyPart scope)
    activeAxisReferences : List (Axis scope)
    value : RelationValue Scalar
    consumerQuestion : String
    relationshipProvenance : List String
    evidenceAndQualificationReference : String
    unresolvedInteractionReference : String

open HigherOrderStudyRelation public

-- Each proposed relation belongs to a full accounted world. Merely
-- enumerating pairwise interactions, attaching canonical Crenshaw
-- certificates, or having a source genealogy is not enough.
record SituatedWorldRelation
  (scope : StudyWorldScope)
  (Scalar : Set) : Set₂ where
  constructor situated-world-relation
  field
    world : AccountedStudyWorld scope
    relation : HigherOrderStudyRelation scope Scalar

open SituatedWorldRelation public

-- Reuse the actual sheaf-like typed hyperfabric, not a new edge/stalk ABI.
-- We DO NOT force a global section when local evidence conflicts.
record ResearchFabricProjection
  (scope : StudyWorldScope)
  (Vertex Edge : Set) : Set₂ where
  constructor research-fabric-projection
  field
    world : AccountedStudyWorld scope
    fabric : Hyper.TypedHyperfabric Vertex Edge
    locatePart : StudyPart scope → Vertex
    -- Flattening two differently identified study parts into one vertex
    -- would lose the very observational distinction this projection needs.
    locatePartPreservesIdentity :
      (left right : StudyPart scope) →
      locatePart left ≡ locatePart right → left ≡ right
    provenancePreservationReceipt : String
    projectionScopeReceipt : String

open ResearchFabricProjection public

-- An observation can share all coarse labels with another world while
-- differing in the answer. Only application-owned FactorsThrough witnesses
-- can license a lossy consumer projection.
data ConsumerProjectionVerdict
    {World Coarse Answer : Set}
    (projection : World → Coarse)
    (question : World → Answer) : Set₁ where
  sufficient :
    Factor.FactorsThrough projection question →
    ConsumerProjectionVerdict projection question
  obstructed :
    Factor.NonFactorabilityWitness projection question →
    ConsumerProjectionVerdict projection question
  unresolvedProjection :
    String → ConsumerProjectionVerdict projection question

-- A source-registered paper or a 19-coordinate SLR candidate packet alone
-- cannot construct an AccountedStudyWorld or ReviewedPartAxisEvidence.
data CandidateCorpusImpliesReviewedPartAxis : Set where

candidateCorpusDoesNotProvePartAxisReview :
  CandidateCorpusImpliesReviewedPartAxis → ⊥
candidateCorpusDoesNotProvePartAxisReview ()
