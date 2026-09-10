module DASHI.Wikimedia.JInvariantWikipediaImage369ReconstructionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Moonshine.JInvariantImageFractalSourceAtlasExact as SourceAtlas
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369ReproductionBundleExact as Reproduction
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Wikimedia.IbrahimBase369JOEISMoonshineSnowballExact as JGraph
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- J-INVARIANT WIKIPEDIA IMAGE / 369 RECONSTRUCTION SNOWBALL
--
-- This owner corrects a weaker reading of the J-image lane. The repo already
-- owns a formulaic reconstruction architecture for the phase image:
--
--   z -> J(z)=g2^3/Delta -> Re/Im -> atan2 phase
--     -> continuous colour/tone -> C3/C6/C9/C27 observers.
--
-- The Wikimedia phase image is therefore not merely a visual analogy. It is a
-- source-attributed target of an existing same-object reconstruction pipeline.
-- What remains open is the concrete analytic/raster producer and pixelwise
-- comparison receipt, not the semantic reconstruction architecture.
------------------------------------------------------------------------

jInvariantQid : Identity.ExternalIdentityDemand
jInvariantQid = JGraph.jInvariantQid

domainColoringQid : Identity.ExternalIdentityDemand
domainColoringQid = Identity.mkOptionalIdentityDemand
  "J-image reconstruction snowball"
  "domain-coloring visualization identity"
  "domain coloring"
  Identity.wikidataQid
  (Identity.verified "Q5289811" "Wikidata oldid 2479624317 inspected 2026-09-10")

phaseImageCommons : Identity.ExternalIdentityDemand
phaseImageCommons = Identity.mkOptionalIdentityDemand
  "J-image reconstruction snowball"
  "phase image source identity"
  "J-inv-phase.jpeg"
  Identity.canonicalURL
  (Identity.verified
    "https://commons.wikimedia.org/wiki/File:J-inv-phase.jpeg"
    "Linas Vepstas; original upload 2005-02-15; Commons description inspected 2026-09-10")

kleinComplexImageCommons : Identity.ExternalIdentityDemand
kleinComplexImageCommons = Identity.mkOptionalIdentityDemand
  "J-image reconstruction snowball"
  "Klein complex-plane image source identity"
  "KleinInvariantJ.jpg"
  Identity.canonicalURL
  (Identity.verified
    "https://commons.wikimedia.org/wiki/File:KleinInvariantJ.jpg"
    "Jan Homann; upload 2007-08-03; public-domain source description inspected 2026-09-10")

------------------------------------------------------------------------
-- Existing same-object reconstruction architecture retained.
------------------------------------------------------------------------

record JImageReconstructionStatus : Set where
  constructor j-image-reconstruction-status
  field
    sourceImageAttributed : Bool
    kleinJFormulaOwned : Bool
    realImaginaryProjectionOwned : Bool
    atan2PhaseOwned : Bool
    continuousPhaseRetained : Bool
    colourToneSurfaceOwned : Bool
    C3ObserverOwned : Bool
    C6ObserverOwned : Bool
    C9ObserverOwned : Bool
    C27ObserverOwned : Bool
    pixelToColourSurfaceOwned : Bool
    modularReplicationCompilerOwned : Bool
    concreteComplexNumericsPaid : Bool
    concreteRasterSerializationPaid : Bool
    sourceRasterPixelComparisonPaid : Bool
open JImageReconstructionStatus public

currentJImageReconstructionStatus : JImageReconstructionStatus
currentJImageReconstructionStatus =
  j-image-reconstruction-status
    true true true true true true true true true true true true
    false false false

rendererFrontier : Render.FormulaicRendererFrontier
rendererFrontier = Render.canonicalFormulaicRendererFrontier

reproductionFrontier : Reproduction.ReproductionBundleFrontier
reproductionFrontier = Reproduction.canonicalReproductionBundleFrontier

kleinConstructionBoundary : Klein.KleinJGluingBidiFrontier
kleinConstructionBoundary = Klein.canonicalKleinJGluingBidiFrontier

sourceBoundary : SourceAtlas.JImageAttributionBoundary
sourceBoundary = SourceAtlas.canonicalJImageAttributionBoundary

------------------------------------------------------------------------
-- Visual dimensions/fibres.
------------------------------------------------------------------------

data VisualCoordinate : Set where
  analyticPoint complexValue realPart imaginaryPart continuousPhase tone hue
  modularFundamentalDomain phaseWinding gluingState observer3 observer6 observer9 observer27 : VisualCoordinate

record VisualFibreRole : Set where
  constructor visual-fibre-role
  field
    coordinate : VisualCoordinate
    role : String
    sourceDescribed : Bool
    repoConstructed : Bool
    createsAnalyticProof : Bool
open VisualFibreRole public

phaseRole : VisualFibreRole
phaseRole = visual-fibre-role continuousPhase
  "atan2(Im J, Re J), retained before finite Base369 observation"
  true true false

tripleWindingRole : VisualFibreRole
tripleWindingRole = visual-fibre-role phaseWinding
  "source describes threefold winding around cubic zeros"
  true true false

observer27Role : VisualFibreRole
observer27Role = visual-fibre-role observer27
  "finite 27-state observation of the same continuous phase payload"
  false true false

------------------------------------------------------------------------
-- All-pairs / FactorsThrough consequences.
------------------------------------------------------------------------

record VisualFactorsThroughCandidate : Set where
  constructor visual-factors-through-candidate
  field
    sourceSurface : String
    proposedObserver : String
    preservesExactValue : Bool
    preservesExactPhase : Bool
    sufficientForSourceRaster : Bool
    collisionMaySnowballMissingAxis : Bool
open VisualFactorsThroughCandidate public

phaseThroughObserver27 : VisualFactorsThroughCandidate
phaseThroughObserver27 = visual-factors-through-candidate
  "continuous j phase"
  "C27 observer"
  false false false true

phaseThroughFullRenderSample : VisualFactorsThroughCandidate
phaseThroughFullRenderSample = visual-factors-through-candidate
  "continuous j phase"
  "J369RenderSample retaining exact value/phase/tone plus 3/6/9/27 observers"
  true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceImageCreatesBase369Theorem : Set where
data Observer27ReconstructsContinuousPhaseAlone : Set where
data VisualSimilarityCreatesSameFunction : Set where
data DomainColoringQidCreatesJInvariantIdentity : Set where
data FormulaicArchitectureEqualsPixelwiseReproductionReceipt : Set where

sourceImageDoesNotCreateBase369Theorem : SourceImageCreatesBase369Theorem → ⊥
sourceImageDoesNotCreateBase369Theorem ()

observer27DoesNotRecoverContinuousPhase : Observer27ReconstructsContinuousPhaseAlone → ⊥
observer27DoesNotRecoverContinuousPhase ()

visualSimilarityDoesNotCreateSameFunction : VisualSimilarityCreatesSameFunction → ⊥
visualSimilarityDoesNotCreateSameFunction ()

domainColoringDoesNotCreateJIdentity : DomainColoringQidCreatesJInvariantIdentity → ⊥
domainColoringDoesNotCreateJIdentity ()

architectureIsNotPixelComparison : FormulaicArchitectureEqualsPixelwiseReproductionReceipt → ⊥
architectureIsNotPixelComparison ()

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
