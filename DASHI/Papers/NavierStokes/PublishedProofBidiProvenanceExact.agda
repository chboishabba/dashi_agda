module DASHI.Papers.NavierStokes.PublishedProofBidiProvenanceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SEPTEMBER 2026 NAVIER--STOKES PUBLISHED-PROOF BIDI PROVENANCE BOUNDARY
--
-- Purpose
-- -------
-- Retain the historical DASHI proof search and compare it bidirectionally with
-- the September 2026 published OpenAI/Lean forced-blowup result WITHOUT
-- collapsing distinct Clay alternatives or importing an external theorem as
-- proof of a DASHI statement.
--
-- The released result establishes forced breakdown alternatives C/D.  The
-- live DASHI Paper-1 programme has targeted unforced periodic global
-- regularity (alternative B).  They belong to the same Clay problem family,
-- but they are not the same statement, quantifier direction, forcing regime,
-- or conclusion.
--
-- The merged PR #890 additionally supplied an internal negative control for a
-- naive geometry-only same-output separation strategy: fixed-output slot
-- geometry is many-to-one with respect to the literal observable kernel when
-- velocity arguments coincide.  That failed route remains provenance and is
-- not silently deleted.
------------------------------------------------------------------------

data ClayAlternative : Set where
  existenceSmoothnessR3 : ClayAlternative
  existenceSmoothnessPeriodic : ClayAlternative
  forcedBreakdownR3 : ClayAlternative
  forcedBreakdownPeriodic : ClayAlternative

data ForcingRegime : Set where
  unforced : ForcingRegime
  smoothExternalForce : ForcingRegime

data ProofRelationship : Set where
  sameStatement : ProofRelationship
  sameProblemFamilyDifferentStatement : ProofRelationship
  representationDonor : ProofRelationship
  provenanceOnly : ProofRelationship

data ConstructionStatus : Set where
  constructed : ConstructionStatus
  sourceWrittenUncertified : ConstructionStatus
  openConstruction : ConstructionStatus
  rejectedRoute : ConstructionStatus

record TheoremCoordinate : Set where
  constructor theorem-coordinate
  field
    alternative : ClayAlternative
    forcing : ForcingRegime
    initialDataDescription : String
    conclusionDescription : String

open TheoremCoordinate public

openAIPublishedWholeSpaceCoordinate : TheoremCoordinate
openAIPublishedWholeSpaceCoordinate =
  theorem-coordinate
    forcedBreakdownR3
    smoothExternalForce
    "there exist smooth initial data and smooth forcing; the released paper also gives a zero-initial-data construction"
    "no global smooth solution with the required physical bounds exists"

openAIPublishedPeriodicCoordinate : TheoremCoordinate
openAIPublishedPeriodicCoordinate =
  theorem-coordinate
    forcedBreakdownPeriodic
    smoothExternalForce
    "there exist smooth periodic initial data and smooth periodic forcing; the released periodic corollary is constructed from the whole-space candidate"
    "no global smooth periodic solution exists"

dashiLivePaperOneCoordinate : TheoremCoordinate
dashiLivePaperOneCoordinate =
  theorem-coordinate
    existenceSmoothnessPeriodic
    unforced
    "arbitrary admissible smooth divergence-free periodic initial data"
    "global smooth periodic continuation / no finite-time singularity"

------------------------------------------------------------------------
-- External source atlas.  Citation records provenance only.
------------------------------------------------------------------------

openAIPublicationSource : Source.AttributedSource
openAIPublicationSource =
  Source.mkNoDOISource
    "OpenAI"
    "On the Navier-Stokes Millennium Prize Problem / Finite time blowup for Navier-Stokes"
    "OpenAI research publication and released manuscript"
    "2026"
    "https://openai.com/index/navier-stokes-solution/"
    (Source.namedSourceKind "research publication")
    "Primary source for the September 8, 2026 forced-breakdown claim; retained as an external theorem source, not as proof of DASHI's unforced regularity target."
    Source.publicAttribution

openAILeanSource : Source.AttributedSource
openAILeanSource =
  Source.mkNoDOISource
    "OpenAI"
    "NavierStokesAndEuler Lean certificates"
    "GitHub repository, formal proof commit 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"
    "2026"
    "https://github.com/openai/NavierStokesAndEuler/commit/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"
    (Source.namedSourceKind "machine-checked formalization")
    "External formal certificate for the published forced-breakdown theorem. It is a bidirectional comparison target and does not discharge a DASHI theorem unless a same-object theorem is separately constructed."
    Source.publicAttribution

clayProblemSource : Source.AttributedSource
clayProblemSource =
  Source.mkNoDOISource
    "Charles L. Fefferman / Clay Mathematics Institute"
    "Existence and Smoothness of the Navier-Stokes Equation"
    "Official Millennium Prize problem description"
    "2000"
    "https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf"
    Source.institutionalSource
    "Defines the four accepted alternatives A--D. Used only to type the theorem-family distinction."
    Source.publicAttribution

publishedProofSources : List Source.AttributedSource
publishedProofSources =
  openAIPublicationSource ∷ openAILeanSource ∷ clayProblemSource ∷ []

publishedProofAtlas : Source.AttributedSourceAtlas
publishedProofAtlas =
  Source.mkSourceAtlas
    "September 2026 Navier-Stokes published-proof bidi atlas"
    "DASHI.Papers.NavierStokes.PublishedProofBidiProvenanceExact"
    publishedProofSources
    "Primary external sources for comparing the released forced-breakdown theorem with DASHI's historical and live Navier-Stokes proof programmes. The atlas imports neither proof nor authority."

------------------------------------------------------------------------
-- Exact non-promotion / theorem-family firewall.
------------------------------------------------------------------------

publishedProofRelationshipToDashiLiveTarget : ProofRelationship
publishedProofRelationshipToDashiLiveTarget = sameProblemFamilyDifferentStatement

publishedForcedBlowupRecorded : Bool
publishedForcedBlowupRecorded = true

publishedForcedBlowupSameStatementAsDashiUnforcedRegularity : Bool
publishedForcedBlowupSameStatementAsDashiUnforcedRegularity = false

sameForcingRegime : Bool
sameForcingRegime = false

sameQuantifierDirection : Bool
sameQuantifierDirection = false

sameConclusion : Bool
sameConclusion = false

sameClayProblemFamily : Bool
sameClayProblemFamily = true

externalCitationImportsProof : Bool
externalCitationImportsProof = false

------------------------------------------------------------------------
-- Historical/internal provenance.
------------------------------------------------------------------------

historicalA1A9RouteRetained : Bool
historicalA1A9RouteRetained = true

historicalA1A9RouteStatus : ConstructionStatus
historicalA1A9RouteStatus = openConstruction

modernR568RouteStatus : ConstructionStatus
modernR568RouteStatus = openConstruction

pr890SameObjectDifferencePlumbingStatus : ConstructionStatus
pr890SameObjectDifferencePlumbingStatus = constructed

-- PR #890's merged negative-control result: distinct fixed-output incidence
-- geometry alone cannot force slot separation because the observable kernel is
-- many-to-one in geometry when the velocity arguments coincide.
pr890GeometryOnlySeparationSufficient : Bool
pr890GeometryOnlySeparationSufficient = false

pr890GeometryOnlyRouteStatus : ConstructionStatus
pr890GeometryOnlyRouteStatus = rejectedRoute

------------------------------------------------------------------------
-- Bidirectional comparison gate.
--
-- Forward direction asks which released-paper constructions can be rebuilt
-- from pre-existing DASHI owners with dates/commits retained.
-- Reverse direction asks which DASHI objects correspond to actual dependencies
-- of the released proof.  Neither direction is assumed from vocabulary or
-- visual similarity.
------------------------------------------------------------------------

dashiConstructsPublishedForcedBlowupProof : Bool
dashiConstructsPublishedForcedBlowupProof = false

publishedProofConstructsDashiUnforcedRegularity : Bool
publishedProofConstructsDashiUnforcedRegularity = false

bidiSameObjectWeldComplete : Bool
bidiSameObjectWeldComplete = false

dashiUnforcedPeriodicClayPromotion : Bool
dashiUnforcedPeriodicClayPromotion = false

publishedForcedBlowupRecordedIsTrue : publishedForcedBlowupRecorded ≡ true
publishedForcedBlowupRecordedIsTrue = refl

publishedForcedBlowupSameStatementAsDashiUnforcedRegularityIsFalse :
  publishedForcedBlowupSameStatementAsDashiUnforcedRegularity ≡ false
publishedForcedBlowupSameStatementAsDashiUnforcedRegularityIsFalse = refl

externalCitationImportsProofIsFalse : externalCitationImportsProof ≡ false
externalCitationImportsProofIsFalse = refl

historicalA1A9RouteRetainedIsTrue : historicalA1A9RouteRetained ≡ true
historicalA1A9RouteRetainedIsTrue = refl

pr890GeometryOnlySeparationSufficientIsFalse :
  pr890GeometryOnlySeparationSufficient ≡ false
pr890GeometryOnlySeparationSufficientIsFalse = refl

dashiConstructsPublishedForcedBlowupProofIsFalse :
  dashiConstructsPublishedForcedBlowupProof ≡ false
dashiConstructsPublishedForcedBlowupProofIsFalse = refl

dashiUnforcedPeriodicClayPromotionIsFalse :
  dashiUnforcedPeriodicClayPromotion ≡ false
dashiUnforcedPeriodicClayPromotionIsFalse = refl
