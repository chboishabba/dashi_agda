{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStepVConnectedCorrelationSourceSnowballExact where

------------------------------------------------------------------------
-- STEP-V CONNECTED-CORRELATION SOURCE SNOWBALL
--
-- Highest-alpha purpose:
--   preserve the live mathematical consumer while attaching primary-source
--   lineage and search coordinates without promoting citations into proof.
--
-- Live branch archaeology has already reduced the source-native Step-V route
-- below the broad phrase "quantitative clustering":
--
--   KP convergence
--     -> cluster-weight exponential decay
--     -> two-mark connected-cluster representation/support
--     -> absolute connecting-cluster weight tail
--     -> physical separation/rate transport
--     -> same-family continuum/OS clustering
--     -> spectral-gap compiler.
--
-- The direct theorem-bearing Step-V payment on the current two-mark carrier is
-- therefore the connecting-weight tail, together with the same-object
-- representation/support welds required to apply it.  The source records below
-- identify theorem lineage only.  They DO NOT inhabit those fields.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _≤_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.YangMills.BalabanLargeFieldStepV as StepV
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked

------------------------------------------------------------------------
-- Primary-source atlas.
------------------------------------------------------------------------

koteckyPreiss1986 : Source.AttributedSource
koteckyPreiss1986 =
  Source.mkDOISource
    "Roman Kotecky; David Preiss"
    "Cluster expansion for abstract polymer models"
    "Communications in Mathematical Physics 103, 491--498"
    "1986"
    "10.1007/BF01211762"
    "https://doi.org/10.1007/BF01211762"
    Source.academicArticleSource
    "primary abstract-polymer convergence/tail authority; motivates KP -> absolutely convergent cluster expansion, but does not instantiate the Yang--Mills two-mark carrier"
    Source.publicAttribution

ueltschi2004 : Source.AttributedSource
ueltschi2004 =
  Source.mkDOISource
    "Daniel Ueltschi"
    "Cluster expansions and correlation functions"
    "Moscow Mathematical Journal 4(2), 511--522"
    "2004"
    "10.17323/1609-4514-2004-4-2-511-522"
    "https://doi.org/10.17323/1609-4514-2004-4-2-511-522"
    Source.academicArticleSource
    "primary correlation-expansion theorem-shape source; develops expressions and estimates for correlation functions including a lattice polymer model; same-object Yang--Mills instantiation remains separate"
    Source.publicAttribution

balabanCMP116 : Source.AttributedSource
balabanCMP116 =
  Source.mkDOISource
    "Tadeusz Balaban"
    "Renormalization Group Approach to Lattice Gauge Field Theories. II. Cluster Expansions"
    "Communications in Mathematical Physics 116, 1--22"
    "1988"
    "10.1007/BF01239022"
    "https://doi.org/10.1007/BF01239022"
    Source.academicArticleSource
    "primary Yang--Mills-native cluster-expansion source context; does not by title/citation alone inhabit the repository's literal two-mark connected-response or connecting-tail fields"
    Source.publicAttribution

stepVConnectedCorrelationPrimaryAtlas : Source.AttributedSourceAtlas
stepVConnectedCorrelationPrimaryAtlas =
  Source.mkSourceAtlas
    "Yang--Mills Step-V connected-correlation primary-source snowball"
    "DASHI.Physics.YangMills.BalabanStepVConnectedCorrelationSourceSnowballExact"
    (koteckyPreiss1986 ∷ ueltschi2004 ∷ balabanCMP116 ∷ [])
    "source lineage for KP convergence, polymer correlation expansions, and the Yang--Mills cluster-expansion carrier; citations are non-promoting and do not discharge same-object physical leaves"

------------------------------------------------------------------------
-- Search coordinates.  These are deliberately weaker than source authority.
------------------------------------------------------------------------

record SearchCoordinate : Set where
  constructor searchCoordinate
  field
    label : String
    value : String
    status : String
    semanticRole : String

open SearchCoordinate public

romanKoteckyQid : SearchCoordinate
romanKoteckyQid =
  searchCoordinate
    "Wikidata QID: Roman Kotecky"
    "Q57054683"
    "web-verified"
    "author identity coordinate only"

davidPreissQid : SearchCoordinate
davidPreissQid =
  searchCoordinate
    "Wikidata QID: David Preiss"
    "Q720518"
    "web-verified"
    "author identity coordinate only"

koteckyPreissPaperQid : SearchCoordinate
koteckyPreissPaperQid =
  searchCoordinate
    "Wikidata QID: Kotecky--Preiss 1986 paper"
    "unresolved"
    "not located in current source snowball"
    "do not guess a paper QID from author or DOI identity"

danielUeltschiQid : SearchCoordinate
danielUeltschiQid =
  searchCoordinate
    "Wikidata QID: Daniel Ueltschi"
    "unresolved"
    "not located in current source snowball"
    "do not guess a person QID from name similarity"

ueltschiUDC : SearchCoordinate
ueltschiUDC =
  searchCoordinate
    "UDC coordinates from journal record"
    "82B05; 82B10"
    "primary bibliographic record"
    "statistical mechanics search coordinate; not theorem authority"

stepVDewey : SearchCoordinate
stepVDewey =
  searchCoordinate
    "Dewey coordinate"
    "unresolved"
    "no article-level authoritative Dewey mapping acquired"
    "do not manufacture Dewey from a broad subject guess"

stepVOEIS : SearchCoordinate
stepVOEIS =
  searchCoordinate
    "OEIS coordinate"
    "not-applicable-at-current-consumer"
    "no integer-sequence object is theorem-bearing here"
    "retain OEIS only if a later finite enumeration/count sequence becomes a real producer coordinate"

stepVSearchCoordinates : List SearchCoordinate
stepVSearchCoordinates =
  romanKoteckyQid ∷
  davidPreissQid ∷
  koteckyPreissPaperQid ∷
  danielUeltschiQid ∷
  ueltschiUDC ∷
  stepVDewey ∷
  stepVOEIS ∷
  []

------------------------------------------------------------------------
-- Snowball role classification.
------------------------------------------------------------------------

data SnowballRole : Set where
  primaryConvergenceSource : SnowballRole
  primaryCorrelationExpansionSource : SnowballRole
  primaryYMCarrierSource : SnowballRole
  representationCompiler : SnowballRole
  physicalGeometryLeaf : SnowballRole
  liveQuantitativeTailLeaf : SnowballRole
  downstreamTransportCompiler : SnowballRole

record SnowballNode : Set where
  constructor snowballNode
  field
    nodeName : String
    role : SnowballRole
    conclusionPaying : Bool

open SnowballNode public

kpSourceNode : SnowballNode
kpSourceNode = snowballNode
  "Kotecky--Preiss abstract polymer convergence theorem"
  primaryConvergenceSource
  false

ueltschiCorrelationNode : SnowballNode
ueltschiCorrelationNode = snowballNode
  "Ueltschi correlation-expansion theorem family"
  primaryCorrelationExpansionSource
  false

balabanCMP116Node : SnowballNode
balabanCMP116Node = snowballNode
  "Balaban CMP116 Yang--Mills cluster-expansion source carrier"
  primaryYMCarrierSource
  false

markedLogZCompilerNode : SnowballNode
markedLogZCompilerNode = snowballNode
  "mixed marked log-partition derivative = connected correlation"
  representationCompiler
  false

twoMarkRepresentationNode : SnowballNode
twoMarkRepresentationNode = snowballNode
  "same-carrier two-mark connected-response expansion/support"
  physicalGeometryLeaf
  true

connectingWeightTailNode : SnowballNode
connectingWeightTailNode = snowballNode
  "absolute connecting-cluster weight sum <= configured rooted tail"
  liveQuantitativeTailLeaf
  true

------------------------------------------------------------------------
-- Exact branch-facing theorem-shape exposure.
--
-- We deliberately reuse the existing records rather than defining another
-- clustering ontology.  These aliases make the first Step-V payment visible to
-- proof search without claiming an inhabitant.
------------------------------------------------------------------------

StepVHistoricalCorrelationImplicationShape :
  ∀ {Site Polymer Configuration Bound : Set} →
  (estimates : StepV.LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  Set
StepVHistoricalCorrelationImplicationShape estimates =
  StepV.LargeFieldStepVEstimates.ClusterWeightsExponentiallyDecay estimates →
  StepV.LargeFieldStepVEstimates.ConnectedCorrelationsClusterBound estimates

stepVHistoricalCorrelationImplicationStoredAsField :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : StepV.LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  StepVHistoricalCorrelationImplicationShape estimates
stepVHistoricalCorrelationImplicationStoredAsField estimates =
  StepV.LargeFieldStepVEstimates.connectedCorrelationTheorem estimates

TwoMarkLivePaymentShape : ∀ {Cutoff Observable Cluster : Set} →
  TwoMark.TwoMarkedConnectedClusterTail Cutoff Observable Cluster → Set
TwoMarkLivePaymentShape dataSet =
  ∀ cutoff A B →
    TwoMark.sumℚ
      (TwoMark.map
        (λ cluster → TwoMark.absoluteValue dataSet
          (TwoMark.clusterWeight dataSet cutoff A B cluster))
        (TwoMark.contributingClusters dataSet cutoff A B))
    ≤ Tail.rootedShellTail (TwoMark.supportSeparation dataSet A B)

------------------------------------------------------------------------
-- Fail-closed source/payment boundary.
------------------------------------------------------------------------

record StepVSourceSnowballBoundary : Set where
  constructor stepV-source-snowball-boundary
  field
    citationImportsKPProof : Bool
    citationImportsKPProofIsFalse : citationImportsKPProof ≡ false

    citationImportsConnectedCorrelationProof : Bool
    citationImportsConnectedCorrelationProofIsFalse :
      citationImportsConnectedCorrelationProof ≡ false

    qidCreatesSameObjectWeld : Bool
    qidCreatesSameObjectWeldIsFalse : qidCreatesSameObjectWeld ≡ false

    doiCreatesSameObjectWeld : Bool
    doiCreatesSameObjectWeldIsFalse : doiCreatesSameObjectWeld ≡ false

    deweyCreatesTheoremContent : Bool
    deweyCreatesTheoremContentIsFalse : deweyCreatesTheoremContent ≡ false

    oeisMandatoryAtCurrentConsumer : Bool
    oeisMandatoryAtCurrentConsumerIsFalse : oeisMandatoryAtCurrentConsumer ≡ false

    markedLogPartitionIdentityIsCompiler : Bool
    markedLogPartitionIdentityIsCompilerIsTrue :
      markedLogPartitionIdentityIsCompiler ≡ true

    connectingWeightTailIsLiveStepVPayment : Bool
    connectingWeightTailIsLiveStepVPaymentIsTrue :
      connectingWeightTailIsLiveStepVPayment ≡ true

    clusterWeightDecayAlonePaysTwoMarkGeometry : Bool
    clusterWeightDecayAlonePaysTwoMarkGeometryIsFalse :
      clusterWeightDecayAlonePaysTwoMarkGeometry ≡ false

canonicalStepVSourceSnowballBoundary : StepVSourceSnowballBoundary
canonicalStepVSourceSnowballBoundary =
  stepV-source-snowball-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl

sourceAtlasPromotesClaim : Bool
sourceAtlasPromotesClaim = false

sourceAtlasPromotesClaimIsFalse : sourceAtlasPromotesClaim ≡ false
sourceAtlasPromotesClaimIsFalse = refl
