# Digital-ESD hyperfabric — exact-source print, part 1 of 5

**Source ref:** `agent/digital-esd-source-crosspollination-20261101` (2026-11-01). **Role:** attributed snapshot; not a canonical owner, a new theorem or a review-admission result.

This part prints the full text of the source-attribution, factorisation, situated source-audit and evidence-braid owners. The remaining parts print the Alice loom, learning/epistemic governance, ESD transfer, and independently sourced EfS overlay. A module blob SHA is recorded for each source. External published papers are cited by the original attributed registers, not reproduced here.

1. `DASHI/Core/AttributedSourceCore.agda` — SHA 62eb3fa2e0a6fd319ec5d4cc5209c789aba9e464, 189 lines
2. `DASHI/Core/SnowballAttributionProvenanceInvariantExact.agda` — SHA 094aa053fefcc4c44c078518273a75419afadce1, 97 lines
3. `DASHI/Core/QueryFactorisationSufficiency.agda` — SHA 98c592232292bbb6c5f0df047c8df3fd42be30d3, 121 lines
4. `DASHI/Core/IntersectionalNonFactorability.agda` — SHA 55c5f6640096e11cbd2883be66eb5411791d70f9, 161 lines
5. `DASHI/Education/DigitalESDSourceAuditHyperfabricExact.agda` — SHA d71005fdb32888cd32ea4a2272ebc45532439eae, 160 lines
6. `DASHI/Education/DigitalESDSourceAuditAdmissionExact.agda` — SHA 43532b515e9a6fa4478d4d6697b0e0f2957fcc00, 196 lines
7. `DASHI/Education/DigitalESDEvidenceBraidTensionExact.agda` — SHA ead19f7266d4720e06f2ca31c9c1708eaf3e5bb2, 144 lines

## DASHI/Core/AttributedSourceCore.agda

Original source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Core/AttributedSourceCore.agda

Blob SHA: `62eb3fa2e0a6fd319ec5d4cc5209c789aba9e464`.

```agda
module DASHI.Core.AttributedSourceCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable attributed-source surface.
--
-- This is the small common object for author/title/publication/DOI metadata.
-- A citation records provenance and a relationship to a formalisation.  It
-- does not import a theorem, prove agreement, or create domain authority.
------------------------------------------------------------------------

data DOIState : Set where
  doiRecorded : String → DOIState
  noDOIRecordedByAtlas : DOIState

data SourceKind : Set where
  academicArticleSource : SourceKind
  academicBookSource : SourceKind
  academicChapterSource : SourceKind
  practitionerSource : SourceKind
  communitySource : SourceKind
  institutionalSource : SourceKind
  governmentSource : SourceKind
  archivalSource : SourceKind
  technicalStandardSource : SourceKind
  newsSource : SourceKind
  namedSourceKind : String → SourceKind

data AttributionVisibility : Set where
  publicAttribution : AttributionVisibility
  controlledAttribution : AttributionVisibility
  existenceOnlyAttribution : AttributionVisibility

record AttributedSource : Set where
  constructor attributedSource
  field
    sourceAuthor : String
    sourceTitle : String
    publicationContext : String
    publicationYear : String
    doiState : DOIState
    canonicalURL : String
    sourceKind : SourceKind
    formalisationRelationship : String
    attributionVisibility : AttributionVisibility
    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

open AttributedSource public

mkDOISource :
  String → String → String → String → String → String →
  SourceKind → String → AttributionVisibility →
  AttributedSource
mkDOISource author title publication year doi url kind relationship visibility =
  attributedSource
    author
    title
    publication
    year
    (doiRecorded doi)
    url
    kind
    relationship
    visibility
    false
    refl
    false
    refl

mkNoDOISource :
  String → String → String → String → String →
  SourceKind → String → AttributionVisibility →
  AttributedSource
mkNoDOISource author title publication year url kind relationship visibility =
  attributedSource
    author
    title
    publication
    year
    noDOIRecordedByAtlas
    url
    kind
    relationship
    visibility
    false
    refl
    false
    refl

sourceCount : List AttributedSource → Nat
sourceCount [] = zero
sourceCount (_ ∷ sources) = suc (sourceCount sources)

record AttributedSourceAtlas : Set where
  constructor attributedSourceAtlas
  field
    atlasLabel : String
    atlasOwner : String
    sources : List AttributedSource
    atlasScope : String
    absentDOIClaimIsAtlasLocal : Bool
    absentDOIClaimIsAtlasLocalIsTrue : absentDOIClaimIsAtlasLocal ≡ true
    atlasCreatesAuthority : Bool
    atlasCreatesAuthorityIsFalse : atlasCreatesAuthority ≡ false

open AttributedSourceAtlas public

mkSourceAtlas :
  String → String → List AttributedSource → String →
  AttributedSourceAtlas
mkSourceAtlas label owner entries scope =
  attributedSourceAtlas
    label
    owner
    entries
    scope
    true
    refl
    false
    refl

attributedSourceAtlasReceipt :
  AttributedSourceAtlas →
  String →
  GenericReceipt.GenericReceipt
attributedSourceAtlasReceipt atlas validation =
  GenericReceipt.mkNonPromotingReceipt
    (atlasLabel atlas)
    (atlasOwner atlas)
    "attributed source atlas"
    (atlasScope atlas)
    "source identity does not import proof, agreement, endorsement, exhaustive coverage, or domain authority"
    validation

attributedSourceAtlasReceiptNonPromoting :
  (atlas : AttributedSourceAtlas) →
  (validation : String) →
  GenericReceipt.promotesClaim
    (attributedSourceAtlasReceipt atlas validation)
  ≡ false
attributedSourceAtlasReceiptNonPromoting atlas validation = refl

record AttributionProjection
    (source : AttributedSource) : Set where
  constructor attributionProjection
  field
    publicLabel : String
    visibility : AttributionVisibility
    sourceStillIdentified : Bool
    sourceStillIdentifiedIsTrue : sourceStillIdentified ≡ true

open AttributionProjection public

mkPublicAttributionProjection :
  (source : AttributedSource) →
  String →
  AttributionProjection source
mkPublicAttributionProjection source label =
  attributionProjection label publicAttribution true refl

mkControlledAttributionProjection :
  (source : AttributedSource) →
  String →
  AttributionProjection source
mkControlledAttributionProjection source label =
  attributionProjection label controlledAttribution true refl

canonicalAttributedSourceCoreReceipt : GenericReceipt.GenericReceipt
canonicalAttributedSourceCoreReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "reusable attributed source core"
    "DASHI.Core.AttributedSourceCore"
    "AttributedSource / AttributedSourceAtlas / AttributionProjection"
    "centralises author, title, publication, DOI state, canonical URL, source kind, relationship, attribution visibility, and a generic atlas receipt adapter"
    "a source citation does not import proof, agreement, endorsement, cultural authority, scientific authority, legal authority, or political authority"
    "agda -i . DASHI/Core/AttributedSourceCore.agda"

canonicalAttributedSourceCoreReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalAttributedSourceCoreReceipt ≡ false
canonicalAttributedSourceCoreReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse canonicalAttributedSourceCoreReceipt
```

## DASHI/Core/SnowballAttributionProvenanceInvariantExact.agda

Original source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Core/SnowballAttributionProvenanceInvariantExact.agda

Blob SHA: `094aa053fefcc4c44c078518273a75419afadce1`.

```agda
module DASHI.Core.SnowballAttributionProvenanceInvariantExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballPluralLensInvariantExact as Lens

------------------------------------------------------------------------
-- ATTRIBUTION / PROVENANCE AS A SNOWBALL INSTANCE
--
-- AttributedSourceCore and the plural lens are slightly different surfaces:
-- the former names source identity/role/visibility; the latter requires every
-- locally relevant coordinate to survive projection. This module makes source
-- role one concrete instantiation of the abstract invariant.
------------------------------------------------------------------------

data AttributionAxis : Set where
  authorAxis : AttributionAxis
  titleAxis : AttributionAxis
  publicationAxis : AttributionAxis
  doiAxis : AttributionAxis
  canonicalURLAxis : AttributionAxis
  sourceKindAxis : AttributionAxis
  formalisationRelationshipAxis : AttributionAxis
  visibilityAxis : AttributionAxis
  proofImportAxis : AttributionAxis
  authorityAxis : AttributionAxis

attributionRelevant : AttributionAxis → Bool
attributionRelevant _ = true

attributionRetained : AttributionAxis → Bool
attributionRetained _ = true

canonicalAttributionLens : Lens.PluralLens AttributionAxis
canonicalAttributionLens = Lens.plural-lens attributionRelevant attributionRetained (λ _ _ → refl)

record SourceRoleSnowballReceipt (source : Attribution.AttributedSource) : Set where
  constructor source-role-snowball-receipt
  field
    sourceIdentityRetained : Bool
    sourceKindRetained : Bool
    formalisationRelationshipRetained : Bool
    attributionVisibilityRetained : Bool
    proofNonImportRetained : Bool
    authorityNonCreationRetained : Bool
    futureSourceRoleAxesMayBeAdded : Bool
open SourceRoleSnowballReceipt public

canonicalSourceRoleSnowballReceipt :
  (source : Attribution.AttributedSource) → SourceRoleSnowballReceipt source
canonicalSourceRoleSnowballReceipt source =
  source-role-snowball-receipt true true true true true true true

------------------------------------------------------------------------
-- A source proposition/atom may therefore be admitted only with the provenance
-- coordinates required by its consumer. DOI/title/URL are identity coordinates;
-- source kind, relationship and visibility are role coordinates. None promotes
-- the proposition into proof or downstream authority.
------------------------------------------------------------------------

data CitationCreatesProof : Set where
data CitationCreatesDomainAuthority : Set where
data SourceKindCanBeDroppedAfterProjection : Set where
data FormalisationRelationshipCanBeDroppedAfterProjection : Set where
data AttributionVisibilityCanBeDroppedAfterProjection : Set where

citationDoesNotCreateProof : CitationCreatesProof → ⊥
citationDoesNotCreateProof ()

citationDoesNotCreateAuthority : CitationCreatesDomainAuthority → ⊥
citationDoesNotCreateAuthority ()

sourceKindMustSnowballWhenRelevant : SourceKindCanBeDroppedAfterProjection → ⊥
sourceKindMustSnowballWhenRelevant ()

relationshipMustSnowballWhenRelevant : FormalisationRelationshipCanBeDroppedAfterProjection → ⊥
relationshipMustSnowballWhenRelevant ()

visibilityMustSnowballWhenRelevant : AttributionVisibilityCanBeDroppedAfterProjection → ⊥
visibilityMustSnowballWhenRelevant ()

record AttributionSnowballBoundary : Set where
  constructor attribution-snowball-boundary
  field
    attributionInstantiatesPluralLens : Bool
    attributionAndPluralLensAreIdenticalStructures : Bool
    sourceRolesMaySnowball : Bool
    citationMayPromoteProof : Bool
    citationMayCreateAuthority : Bool
open AttributionSnowballBoundary public

canonicalAttributionSnowballBoundary : AttributionSnowballBoundary
canonicalAttributionSnowballBoundary =
  attribution-snowball-boundary true false true false false
```

## DASHI/Core/QueryFactorisationSufficiency.agda

Original source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Core/QueryFactorisationSufficiency.agda

Blob SHA: `98c592232292bbb6c5f0df047c8df3fd42be30d3`.

```agda
module DASHI.Core.QueryFactorisationSufficiency where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- QUERY FACTORISATION SUFFICIENCY
--
-- Classical statistical sufficiency motivates the separation between a
-- reduction that preserves every authorised present query and a claim that the
-- represented model exhausts the underlying world.  DASHI uses the more
-- general factorisation surface below; no probabilistic model is assumed.
--
-- Reference / motivation:
--   R. A. Fisher's sufficient-statistic tradition; this file intentionally
--   cites the concept rather than attributing the generic factorisation theorem
--   below to a particular statistics paper.
--
-- Core law:
--
--   q = qbar o pi
--
-- means q can be answered entirely from the quotient pi.  It says nothing
-- about world/model completeness and nothing about future dynamic safety.
------------------------------------------------------------------------

record InquiryQuestionFamily (State Query : Set) : Set₁ where
  constructor inquiryQuestionFamily
  field
    Answer : Query → Set
    ask : (query : Query) → State → Answer query

open InquiryQuestionFamily public

record FactorsThrough
    {State Surface Query : Set}
    (questions : InquiryQuestionFamily State Query)
    (project : State → Surface)
    (query : Query) : Set₁ where
  constructor factorsThrough
  field
    quotientAnswer : Surface → Answer questions query
    factorisation :
      (state : State) →
      ask questions query state ≡ quotientAnswer (project state)

open FactorsThrough public

record StaticSufficient
    {State Surface Query : Set}
    (questions : InquiryQuestionFamily State Query)
    (project : State → Surface) : Set₁ where
  constructor staticSufficient
  field
    factorFor :
      (query : Query) →
      FactorsThrough questions project query

open StaticSufficient public

------------------------------------------------------------------------
-- Static sufficiency and world coverage are differently typed obligations.
-- There is deliberately no constructor from StaticSufficient to the separate
-- ConsumerIndexedRelevanceMeasure.WorldCoverageWitness surface.
------------------------------------------------------------------------

data StaticSufficiencyWorldCoveragePermission : Set where

staticSufficiencyCannotManufactureWorldCoverage :
  StaticSufficiencyWorldCoveragePermission → ⊥
staticSufficiencyCannotManufactureWorldCoverage ()

------------------------------------------------------------------------
-- Finite witness: a quotient can be exactly sufficient for the only authorised
-- present query while still carrying a hidden state distinction.
------------------------------------------------------------------------

data DemoState : Set where
  visibleLeft : DemoState
  visibleRight : DemoState

data DemoSurface : Set where
  sameSurface : DemoSurface

data DemoQuery : Set where
  whoQuestion : DemoQuery

data DemoAnswer : Set where
  johnAnswer : DemoAnswer

demoQuestions : InquiryQuestionFamily DemoState DemoQuery
demoQuestions = inquiryQuestionFamily (λ query → DemoAnswer) askDemo
  where
    askDemo : (query : DemoQuery) → DemoState → DemoAnswer
    askDemo whoQuestion visibleLeft = johnAnswer
    askDemo whoQuestion visibleRight = johnAnswer

demoProject : DemoState → DemoSurface
demoProject visibleLeft = sameSurface
demoProject visibleRight = sameSurface

demoWhoFactors : FactorsThrough demoQuestions demoProject whoQuestion
demoWhoFactors = factorsThrough demoQuotientAnswer proof
  where
    demoQuotientAnswer : DemoSurface → DemoAnswer
    demoQuotientAnswer sameSurface = johnAnswer

    proof :
      (state : DemoState) →
      ask demoQuestions whoQuestion state ≡ demoQuotientAnswer (demoProject state)
    proof visibleLeft = refl
    proof visibleRight = refl

demoProjectionIsStaticallySufficient :
  StaticSufficient demoQuestions demoProject
demoProjectionIsStaticallySufficient = staticSufficient factor
  where
    factor : (query : DemoQuery) → FactorsThrough demoQuestions demoProject query
    factor whoQuestion = demoWhoFactors
```

## DASHI/Core/IntersectionalNonFactorability.agda

Original source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Core/IntersectionalNonFactorability.agda

Blob SHA: `55c5f6640096e11cbd2883be66eb5411791d70f9`.

```agda
module DASHI.Core.IntersectionalNonFactorability where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- INTERSECTIONAL NON-FACTORABILITY
--
-- Reference / conceptual motivation:
--   Kimberle Crenshaw,
--   "Mapping the Margins: Intersectionality, Identity Politics, and Violence
--   against Women of Color", Stanford Law Review 43(6), 1241-1299 (1991).
--   DOI: 10.2307/1229039.
--
-- Crenshaw's structural/political intersectionality motivates the warning that
-- single-axis frames can fail to represent situated phenomena.  The
-- factorisation criterion below is a DASHI mathematical translation, not a
-- theorem attributed to Crenshaw.
--
-- The recharting theorem added below is also generic DASHI mathematics.  It
-- formalises a representation-theoretic point used in the supplied 2026-08-27
-- discussion: once two situated states have already collided under a coarse
-- observer, post-composing that observer with a relabelling/reweighting/chart
-- map cannot recover a phenomenon that distinguishes those states.  A richer
-- observer must add information rather than merely rename the old quotient.
------------------------------------------------------------------------

record FactorsThrough
    {Situated Flat Outcome : Set}
    (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) : Set₁ where
  constructor factorsThrough
  field
    interpretFlat : Flat → Outcome
    factorisation :
      (state : Situated) →
      phenomenon state ≡ interpretFlat (flatten state)

open FactorsThrough public

record NonFactorabilityWitness
    {Situated Flat Outcome : Set}
    (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) : Set₁ where
  constructor nonFactorabilityWitness
  field
    left right : Situated
    sameFlatProjection : flatten left ≡ flatten right
    situatedOutcomesDiffer : phenomenon left ≡ phenomenon right → ⊥

open NonFactorabilityWitness public

witnessRulesOutEveryFlatFactorisation :
  ∀ {Situated Flat Outcome}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  NonFactorabilityWitness flatten phenomenon →
  FactorsThrough flatten phenomenon →
  ⊥
witnessRulesOutEveryFlatFactorisation witness factor =
  situatedOutcomesDiffer witness
    (trans
      (factorisation factor (left witness))
      (trans
        (cong (interpretFlat factor) (sameFlatProjection witness))
        (sym (factorisation factor (right witness)))))

------------------------------------------------------------------------
-- Recharting/post-composition cannot recover information erased by `flatten`.
-- This is stronger than a statement about permutations: the post-map may be
-- any function whatsoever.  If the original observer identifies the witness
-- pair, every observer factoring through it identifies that pair as well.
------------------------------------------------------------------------

postcomposeNonFactorability :
  ∀ {Situated Flat Recharted Outcome}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  (rechart : Flat → Recharted) →
  NonFactorabilityWitness flatten phenomenon →
  NonFactorabilityWitness (λ state → rechart (flatten state)) phenomenon
postcomposeNonFactorability rechart witness =
  nonFactorabilityWitness
    (left witness)
    (right witness)
    (cong rechart (sameFlatProjection witness))
    (situatedOutcomesDiffer witness)

rechartingCannotRecoverErasedPhenomenon :
  ∀ {Situated Flat Recharted Outcome}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  (rechart : Flat → Recharted) →
  NonFactorabilityWitness flatten phenomenon →
  FactorsThrough (λ state → rechart (flatten state)) phenomenon →
  ⊥
rechartingCannotRecoverErasedPhenomenon rechart witness =
  witnessRulesOutEveryFlatFactorisation
    (postcomposeNonFactorability rechart witness)

------------------------------------------------------------------------
-- Concrete carrier-repair witness.
------------------------------------------------------------------------

data SituatedState : Set where
  sameLabelLowPower : SituatedState
  sameLabelHighPower : SituatedState

data FlatSingleAxis : Set where
  sameDemographicLabel : FlatSingleAxis

flatProjection : SituatedState → FlatSingleAxis
flatProjection sameLabelLowPower = sameDemographicLabel
flatProjection sameLabelHighPower = sameDemographicLabel

relationalOutcome : SituatedState → Bool
relationalOutcome sameLabelLowPower = false
relationalOutcome sameLabelHighPower = true

relationalOutcomeDiffers :
  relationalOutcome sameLabelLowPower ≡
  relationalOutcome sameLabelHighPower → ⊥
relationalOutcomeDiffers ()

canonicalIntersectionalNonFactorability :
  NonFactorabilityWitness flatProjection relationalOutcome
canonicalIntersectionalNonFactorability =
  nonFactorabilityWitness
    sameLabelLowPower
    sameLabelHighPower
    refl
    relationalOutcomeDiffers

flatReweightingCannotRepairMissingRelation :
  FactorsThrough flatProjection relationalOutcome → ⊥
flatReweightingCannotRepairMissingRelation =
  witnessRulesOutEveryFlatFactorisation canonicalIntersectionalNonFactorability

canonicalRechartingCannotRepairMissingRelation :
  ∀ {Recharted : Set} →
  (rechart : FlatSingleAxis → Recharted) →
  FactorsThrough (λ state → rechart (flatProjection state)) relationalOutcome →
  ⊥
canonicalRechartingCannotRepairMissingRelation rechart =
  rechartingCannotRecoverErasedPhenomenon
    rechart canonicalIntersectionalNonFactorability

------------------------------------------------------------------------
-- Product-of-single-axis readings are not automatically intersectional.
-- This no-promotion boundary prevents two separately useful consumer surfaces
-- from being promoted to a sufficient situated-intersectional carrier without
-- an application-supplied factorisation witness.
------------------------------------------------------------------------
data SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission : Set where

separateAxisSufficiencyCannotAutoPromote :
  SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission → ⊥
separateAxisSufficiencyCannotAutoPromote ()
```

## DASHI/Education/DigitalESDSourceAuditHyperfabricExact.agda

Original source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDSourceAuditHyperfabricExact.agda

Blob SHA: `d71005fdb32888cd32ea4a2272ebc45532439eae`.

```agda
module DASHI.Education.DigitalESDSourceAuditHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale
import DASHI.Education.DigitalESDSituatedAuditObserverExact as Observer
import DASHI.Education.DigitalESDSourceAuditAdmissibilityExact as Admissibility
import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards
import DASHI.Education.DigitalESDSourceIntersectionalAuditExact as Intersection
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Tension


------------------------------------------------------------------------
-- SITUATED SOURCE-AUDIT HYPERFABRIC
--
-- Thin composition only. LES is a structural donor for multi-axis situated
-- reasoning; no LES empirical proposition is imported as Digital-ESD evidence.
--
-- Same-object rule: every source-bearing child object is explicitly welded to
-- the hyperfabric's indexed source. A top-level source label is not sufficient.
------------------------------------------------------------------------

record SameSourceObservation (source : Attr.AttributedSource) : Set where
  constructor same-source-observation
  field
    observation : Observer.SituatedAuditObservation
    sourceMatches : Observer.source observation ≡ source

open SameSourceObservation public

record SameSourceAdmissibilityFibre (source : Attr.AttributedSource) : Set where
  constructor same-source-admissibility-fibre
  field
    fibre : Admissibility.AdmissibleEvidenceFibre
    fibreSourceMatches :
      Observer.source (Admissibility.observation fibre) ≡ source

open SameSourceAdmissibilityFibre public

record SameSourceIntersectionReceipt (source : Attr.AttributedSource) : Set where
  constructor same-source-intersection-receipt
  field
    intersection : Intersection.IntersectionReceipt
    intersectionSourceMatches : Intersection.source intersection ≡ source

open SameSourceIntersectionReceipt public

record SourceAuditHyperfabric (source : Attr.AttributedSource) : Set where
  constructor source-audit-hyperfabric
  field
    observations : List (SameSourceObservation source)
    admissibilityFibres : List (SameSourceAdmissibilityFibre source)
    standardLenses : List Standards.StandardLens
    intersections : List (SameSourceIntersectionReceipt source)
    tensions : List Tension.TensionReceipt
    scoringProtocolVersion : String
    structuralDonorReading : String

open SourceAuditHyperfabric public

lesStructuralDonorReading : String
lesStructuralDonorReading =
  "LESSituatedSocioEcologicalHyperfabricExact is reused only as a structural precedent for keeping provenance, relation, history and justice coordinates jointly visible. It contributes no empirical Digital-ESD observation by import."

------------------------------------------------------------------------
-- Coarse visibility profile cannot determine full situated audit state.
------------------------------------------------------------------------

data AuditStateWorld : Set where
  sameScoresNoInteraction : AuditStateWorld
  sameScoresInteractionAndTension : AuditStateWorld

data CoarseVisibilityProfile : Set where sameCoarseScores : CoarseVisibilityProfile

data FullAuditState : Set where
  fullStateNoInteraction : FullAuditState
  fullStateInteractionAndTension : FullAuditState

coarseVisibilityProfile : AuditStateWorld → CoarseVisibilityProfile
coarseVisibilityProfile sameScoresNoInteraction = sameCoarseScores
coarseVisibilityProfile sameScoresInteractionAndTension = sameCoarseScores

fullAuditState : AuditStateWorld → FullAuditState
fullAuditState sameScoresNoInteraction = fullStateNoInteraction
fullAuditState sameScoresInteractionAndTension = fullStateInteractionAndTension

fullAuditStatesDiffer :
  fullAuditState sameScoresNoInteraction ≡
  fullAuditState sameScoresInteractionAndTension → ⊥
fullAuditStatesDiffer ()

coarseVisibilityFullStateWitness :
  INF.NonFactorabilityWitness coarseVisibilityProfile fullAuditState
coarseVisibilityFullStateWitness =
  INF.nonFactorabilityWitness
    sameScoresNoInteraction
    sameScoresInteractionAndTension
    refl
    fullAuditStatesDiffer

coarseVisibilityProfileCannotDetermineFullAuditState :
  INF.FactorsThrough coarseVisibilityProfile fullAuditState → ⊥
coarseVisibilityProfileCannotDetermineFullAuditState =
  INF.witnessRulesOutEveryFlatFactorisation coarseVisibilityFullStateWitness

data CoarseVisibilityProfileDeterminesFullAuditState : Set where
data ScoreProfileCreatesEvidenceObject : Set where
data SingleObserverCreatesWholeAuditState : Set where
data StructuralDonorCreatesDomainEvidence : Set where
data TopLevelSourceLabelCreatesSameObjectChildren : Set where

coarseVisibilityProfileDoesNotDetermineFullAuditState :
  CoarseVisibilityProfileDeterminesFullAuditState → ⊥
coarseVisibilityProfileDoesNotDetermineFullAuditState ()

scoreProfileDoesNotCreateEvidenceObject : ScoreProfileCreatesEvidenceObject → ⊥
scoreProfileDoesNotCreateEvidenceObject ()

singleObserverDoesNotCreateWholeAuditState : SingleObserverCreatesWholeAuditState → ⊥
singleObserverDoesNotCreateWholeAuditState ()

structuralDonorDoesNotCreateDomainEvidence : StructuralDonorCreatesDomainEvidence → ⊥
structuralDonorDoesNotCreateDomainEvidence ()

topLevelSourceLabelDoesNotCreateSameObjectChildren :
  TopLevelSourceLabelCreatesSameObjectChildren → ⊥
topLevelSourceLabelDoesNotCreateSameObjectChildren ()

record SourceAuditHyperfabricBoundary : Set where
  constructor source-audit-hyperfabric-boundary
  field
    scoreIsPrimaryEvidenceObject : Bool
    scoreIsPrimaryEvidenceObjectIsFalse : scoreIsPrimaryEvidenceObject ≡ false
    coarseProfileIsFullAuditState : Bool
    coarseProfileIsFullAuditStateIsFalse : coarseProfileIsFullAuditState ≡ false
    structuralCrossPollinationCreatesEmpiricalAuthority : Bool
    structuralCrossPollinationCreatesEmpiricalAuthorityIsFalse :
      structuralCrossPollinationCreatesEmpiricalAuthority ≡ false
    unresolvedTensionMayRemain : Bool
    unresolvedTensionMayRemainIsTrue : unresolvedTensionMayRemain ≡ true
    childSourceIdentityWeldRequired : Bool
    childSourceIdentityWeldRequiredIsTrue : childSourceIdentityWeldRequired ≡ true

open SourceAuditHyperfabricBoundary public

canonicalSourceAuditHyperfabricBoundary : SourceAuditHyperfabricBoundary
canonicalSourceAuditHyperfabricBoundary = source-audit-hyperfabric-boundary
  false refl
  false refl
  false refl
  true refl
  true refl
```

## DASHI/Education/DigitalESDSourceAuditAdmissionExact.agda

Original source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDSourceAuditAdmissionExact.agda

Blob SHA: `43532b515e9a6fa4478d4d6697b0e0f2957fcc00`.

```agda
module DASHI.Education.DigitalESDSourceAuditAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale
import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards
import DASHI.Education.DigitalESDAuditDomainBoundaryReceiptExact as DomainBoundary
import DASHI.Education.DigitalESDSourceAuditHyperfabricExact as Hyperfabric

------------------------------------------------------------------------
-- COMPLETE CORE-AXIS COVERAGE
------------------------------------------------------------------------

record CompleteCoreAxisCoverage (source : Attr.AttributedSource) : Set where
  constructor complete-core-axis-coverage
  field
    educationalOutcomeReceipt : Scale.AxisVisibilityReceipt source
    educationalOutcomeAxisIsCorrect :
      Scale.axis educationalOutcomeReceipt ≡ Scale.educationalOutcomeTransformation

    representationReceipt : Scale.AxisVisibilityReceipt source
    representationAxisIsCorrect :
      Scale.axis representationReceipt ≡ Scale.representationWhoMissing

    disabilityReceipt : Scale.AxisVisibilityReceipt source
    disabilityAxisIsCorrect :
      Scale.axis disabilityReceipt ≡ Scale.disabilityEffectiveAccessibility

    participantAuthorityReceipt : Scale.AxisVisibilityReceipt source
    participantAuthorityAxisIsCorrect :
      Scale.axis participantAuthorityReceipt ≡ Scale.participantVoiceAuthority

    environmentReceipt : Scale.AxisVisibilityReceipt source
    environmentAxisIsCorrect :
      Scale.axis environmentReceipt ≡ Scale.environmentalMaterialLifecycle

    externalityReceipt : Scale.AxisVisibilityReceipt source
    externalityAxisIsCorrect :
      Scale.axis externalityReceipt ≡ Scale.externalityIncidence

    politicalEconomyReceipt : Scale.AxisVisibilityReceipt source
    politicalEconomyAxisIsCorrect :
      Scale.axis politicalEconomyReceipt ≡ Scale.politicalEconomy

    socialProvisioningReceipt : Scale.AxisVisibilityReceipt source
    socialProvisioningAxisIsCorrect :
      Scale.axis socialProvisioningReceipt ≡ Scale.socialProvisioningCommunity

    durabilityReceipt : Scale.AxisVisibilityReceipt source
    durabilityAxisIsCorrect :
      Scale.axis durabilityReceipt ≡ Scale.maintenanceInstitutionalDurability

    contextReceipt : Scale.AxisVisibilityReceipt source
    contextAxisIsCorrect :
      Scale.axis contextReceipt ≡ Scale.contextTransferTimeIntergenerational

open CompleteCoreAxisCoverage public

record StandardApplicabilityDeclaration : Set where
  constructor standard-applicability-declaration
  field
    lens : Standards.StandardLens
    relationship : Standards.StandardRelationship
    reason : String

open StandardApplicabilityDeclaration public

------------------------------------------------------------------------
-- SYNTHESIS ADMISSION
--
-- Marginal score completeness is necessary but insufficient. Every admitted
-- source must also carry all seven thin audit-domain boundary receipts so the
-- hyperfabric remains connected to disability/access, who-is-missing,
-- externality, political-economy, provisioning, durability and material-
-- lifecycle semantics without importing the heavyweight producer worlds.
------------------------------------------------------------------------

record SourceAuditAdmission (source : Attr.AttributedSource) : Set where
  constructor source-audit-admission
  field
    claimCeilingReading : String
    completeCoreCoverage : CompleteCoreAxisCoverage source
    completeDomainBoundaryCoverage :
      DomainBoundary.CompleteDomainBoundaryCoverage source
    hyperfabric : Hyperfabric.SourceAuditHyperfabric source
    standardsApplicability : List StandardApplicabilityDeclaration
    standardsApplicabilityDeclared : Bool
    standardsApplicabilityDeclaredIsTrue : standardsApplicabilityDeclared ≡ true
    requiredIntersectionsChecked : Bool
    requiredIntersectionsCheckedIsTrue : requiredIntersectionsChecked ≡ true
    tensionsPreservedWhenPresent : Bool
    tensionsPreservedWhenPresentIsTrue : tensionsPreservedWhenPresent ≡ true
    provenanceReceipt : Snowball.SourceRoleSnowballReceipt source
    wrongTypePromotionsBlocked : Bool
    wrongTypePromotionsBlockedIsTrue : wrongTypePromotionsBlocked ≡ true
    admissionAdmissibleForSynthesis : Bool
    admissionAdmissibleForSynthesisIsTrue : admissionAdmissibleForSynthesis ≡ true
    scoringProtocolVersion : String

open SourceAuditAdmission public

mkSourceAuditAdmission :
  (source : Attr.AttributedSource) →
  String →
  CompleteCoreAxisCoverage source →
  DomainBoundary.CompleteDomainBoundaryCoverage source →
  Hyperfabric.SourceAuditHyperfabric source →
  List StandardApplicabilityDeclaration →
  String →
  SourceAuditAdmission source
mkSourceAuditAdmission source ceiling coverage domainCoverage hyperfabric standards version =
  source-audit-admission
    ceiling
    coverage
    domainCoverage
    hyperfabric
    standards
    true refl
    true refl
    true refl
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    true refl
    true refl
    version

------------------------------------------------------------------------
-- Admission is a completeness/admissibility gate, not truth or quality.
------------------------------------------------------------------------

data AuthoritativeGrandTotalExists : Set where
data UnscoredSourceEntersSynthesis : Set where
data AuditAdmissionCreatesClaimAuthority : Set where
data AuditAdmissionRaisesClaimCeiling : Set where
data CompleteCoreCoverageCreatesIntersectionalAdequacy : Set where
data DomainBoundaryCoverageImportsProducerWorld : Set where

authoritativeGrandTotalDoesNotExist : AuthoritativeGrandTotalExists → ⊥
authoritativeGrandTotalDoesNotExist ()

unscoredSourceDoesNotEnterSynthesis : UnscoredSourceEntersSynthesis → ⊥
unscoredSourceDoesNotEnterSynthesis ()

auditAdmissionDoesNotCreateClaimAuthority : AuditAdmissionCreatesClaimAuthority → ⊥
auditAdmissionDoesNotCreateClaimAuthority ()

auditAdmissionDoesNotRaiseClaimCeiling : AuditAdmissionRaisesClaimCeiling → ⊥
auditAdmissionDoesNotRaiseClaimCeiling ()

completeCoreCoverageDoesNotCreateIntersectionalAdequacy :
  CompleteCoreCoverageCreatesIntersectionalAdequacy → ⊥
completeCoreCoverageDoesNotCreateIntersectionalAdequacy ()

domainBoundaryCoverageDoesNotImportProducerWorld :
  DomainBoundaryCoverageImportsProducerWorld → ⊥
domainBoundaryCoverageDoesNotImportProducerWorld ()

record SourceAuditAdmissionBoundary : Set where
  constructor source-audit-admission-boundary
  field
    everyAdmittedSourceRequiresCoreCoverage : Bool
    everyAdmittedSourceRequiresCoreCoverageIsTrue :
      everyAdmittedSourceRequiresCoreCoverage ≡ true
    everyAdmittedSourceRequiresDomainBoundaryCoverage : Bool
    everyAdmittedSourceRequiresDomainBoundaryCoverageIsTrue :
      everyAdmittedSourceRequiresDomainBoundaryCoverage ≡ true
    zeroScoresMayStillBeAdmitted : Bool
    zeroScoresMayStillBeAdmittedIsTrue : zeroScoresMayStillBeAdmitted ≡ true
    noAuthoritativeGrandTotal : Bool
    noAuthoritativeGrandTotalIsTrue : noAuthoritativeGrandTotal ≡ true
    admissionEqualsClaimAuthority : Bool
    admissionEqualsClaimAuthorityIsFalse : admissionEqualsClaimAuthority ≡ false
    childSourceIdentityWeldedByType : Bool
    childSourceIdentityWeldedByTypeIsTrue : childSourceIdentityWeldedByType ≡ true
    boundaryReceiptsImportHeavyweightProducerWorlds : Bool
    boundaryReceiptsImportHeavyweightProducerWorldsIsFalse :
      boundaryReceiptsImportHeavyweightProducerWorlds ≡ false

open SourceAuditAdmissionBoundary public

canonicalSourceAuditAdmissionBoundary : SourceAuditAdmissionBoundary
canonicalSourceAuditAdmissionBoundary = source-audit-admission-boundary
  true refl
  true refl
  true refl
  true refl
  false refl
  true refl
  false refl
```

## DASHI/Education/DigitalESDEvidenceBraidTensionExact.agda

Original source: https://github.com/chboishabba/dashi_agda/blob/agent/digital-esd-source-crosspollination-20261101/DASHI/Education/DigitalESDEvidenceBraidTensionExact.agda

Blob SHA: `ead19f7266d4720e06f2ca31c9c1708eaf3e5bb2`.

```agda
module DASHI.Education.DigitalESDEvidenceBraidTensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale

------------------------------------------------------------------------
-- EVIDENCE BRAID / TENSION
--
-- Different admissible observations can converge, complement, remain in
-- productive tension, or remain unresolved. No averaging/fusion is required.
------------------------------------------------------------------------

data BraidRelation : Set where
  convergence : BraidRelation
  complementarity : BraidRelation
  productiveTension : BraidRelation
  unresolvedConflict : BraidRelation
  scopeDifference : BraidRelation
  authorityDifference : BraidRelation
  provenanceDifference : BraidRelation
  prohibitedCollapse : BraidRelation

record TensionReceipt : Set where
  constructor tension-receipt
  field
    leftObservationRef : String
    rightObservationRef : String
    leftProvenanceRef : String
    rightProvenanceRef : String
    relation : BraidRelation
    reasonNotCollapsed : String

open TensionReceipt public

twoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

------------------------------------------------------------------------
-- Finite fixture: same operational availability, different situated access.
------------------------------------------------------------------------

data AvailabilityWorld : Set where
  highAvailabilityEffectiveAccess : AvailabilityWorld
  highAvailabilityBrokenAssistiveWorkflow : AvailabilityWorld

data AvailabilitySurface : Set where highAvailability : AvailabilitySurface

data AccessibilitySurface : Set where effectiveAccess brokenAccess : AccessibilitySurface

availabilityProjection : AvailabilityWorld → AvailabilitySurface
availabilityProjection highAvailabilityEffectiveAccess = highAvailability
availabilityProjection highAvailabilityBrokenAssistiveWorkflow = highAvailability

accessibilityProjection : AvailabilityWorld → AccessibilitySurface
accessibilityProjection highAvailabilityEffectiveAccess = effectiveAccess
accessibilityProjection highAvailabilityBrokenAssistiveWorkflow = brokenAccess

accessibilityDiffers :
  accessibilityProjection highAvailabilityEffectiveAccess ≡
  accessibilityProjection highAvailabilityBrokenAssistiveWorkflow → ⊥
accessibilityDiffers ()

availabilityCannotDetermineAccessibilityWitness :
  INF.NonFactorabilityWitness availabilityProjection accessibilityProjection
availabilityCannotDetermineAccessibilityWitness =
  INF.nonFactorabilityWitness
    highAvailabilityEffectiveAccess
    highAvailabilityBrokenAssistiveWorkflow
    refl
    accessibilityDiffers

availabilityCannotDetermineAccessibility :
  INF.FactorsThrough availabilityProjection accessibilityProjection → ⊥
availabilityCannotDetermineAccessibility =
  INF.witnessRulesOutEveryFlatFactorisation
    availabilityCannotDetermineAccessibilityWitness

availabilityAccessibilityTension : TensionReceipt
availabilityAccessibilityTension = tension-receipt
  "institutional service telemetry: high availability"
  "disabled/access-needs participant observation: assistive workflow broken after change"
  "institutional operational observer"
  "situated participant/access observer"
  productiveTension
  "Both observations may be admissible for different consumers. Averaging them would erase the distinction between operational availability and realised accessibility."

------------------------------------------------------------------------
-- No-promotion / no-fusion firewalls.
------------------------------------------------------------------------

data SharedObservationCreatesSameProvenance : Set where
data CoordinatedUseCreatesEpistemicFusion : Set where
data PluralObservationsCreateForcedConsensus : Set where
data DisagreementCreatesInvalidEvidence : Set where
data SharedScoreCreatesSameSituatedState : Set where

sharedObservationDoesNotCreateSameProvenance :
  SharedObservationCreatesSameProvenance → ⊥
sharedObservationDoesNotCreateSameProvenance ()

coordinatedUseDoesNotCreateEpistemicFusion :
  CoordinatedUseCreatesEpistemicFusion → ⊥
coordinatedUseDoesNotCreateEpistemicFusion ()

pluralObservationsDoNotCreateForcedConsensus :
  PluralObservationsCreateForcedConsensus → ⊥
pluralObservationsDoNotCreateForcedConsensus ()

disagreementDoesNotCreateInvalidEvidence : DisagreementCreatesInvalidEvidence → ⊥
disagreementDoesNotCreateInvalidEvidence ()

sharedScoreDoesNotCreateSameSituatedState : SharedScoreCreatesSameSituatedState → ⊥
sharedScoreDoesNotCreateSameSituatedState ()

record EvidenceBraidBoundary : Set where
  constructor evidence-braid-boundary
  field
    coordinatedUseRequiresFusion : Bool
    coordinatedUseRequiresFusionIsFalse : coordinatedUseRequiresFusion ≡ false
    pluralObservationRequiresConsensusScore : Bool
    pluralObservationRequiresConsensusScoreIsFalse :
      pluralObservationRequiresConsensusScore ≡ false
    tensionMayRemainVisible : Bool
    tensionMayRemainVisibleIsTrue : tensionMayRemainVisible ≡ true

open EvidenceBraidBoundary public

canonicalEvidenceBraidBoundary : EvidenceBraidBoundary
canonicalEvidenceBraidBoundary = evidence-braid-boundary
  false refl
  false refl
  true refl

holdTheTensionReading : String
holdTheTensionReading =
  "Distinct admissible observations may be coordinated without fusion. Convergence does not erase provenance; disagreement need not invalidate either observation; and operational, participant, ecological, political-economic, cultural and standards lenses can remain jointly visible until a declared consumer justifies a more specific relation."
```

