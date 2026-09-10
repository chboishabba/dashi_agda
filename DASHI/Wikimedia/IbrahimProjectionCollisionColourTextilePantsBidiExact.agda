module DASHI.Wikimedia.IbrahimProjectionCollisionColourTextilePantsBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ProjectionFibre as Fibre
import DASHI.Core.ProjectionCategory as PC
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Wikimedia.Ibrahim36927PantsColourTextileSweetgrassSnowballExact as Cross
import DASHI.Wikimedia.IbrahimColourMetamerismProjectionFibreSnowballExact as Metamer
import DASHI.Combinatorics.TextileCrossPollinationExact as Textile
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Interop.SweetgrassCarrierSpine as Sweetgrass

------------------------------------------------------------------------
-- PROJECTION COLLISION / HIDDEN-HISTORY BIDI SNOWBALL
--
-- Common proof shape only:
--
--       detailed carrier/history --projection--> coarse visible coordinate
--              x1 != x2                     pi(x1) = pi(x2)
--
-- Instances come from different domains and are NOT thereby identified:
--   colour: distinct spectra may be metameric under a declared observer;
--   braid: distinct crossing words may share a coarse crossing-count surface;
--   textiles: a common event skeleton loses craft-specific dependency grammar;
--   pants/gluing: local branch coordinates do not manufacture global/smooth
--                 gluing identity;
--   Sweetgrass: braid/fabric language retains cultural attribution/provenance
--               and is not reducible to a mathematical braid word.
------------------------------------------------------------------------

data CollisionDomain : Set where
  spectralColourDomain : CollisionDomain
  braidHistoryDomain : CollisionDomain
  textileCraftDomain : CollisionDomain
  pantsGluingDomain : CollisionDomain
  culturalProvenanceDomain : CollisionDomain

record ProjectionCollisionPattern : Set where
  constructor projection-collision-pattern
  field
    domain : CollisionDomain
    detailedCarrierReference : String
    projectionReference : String
    coarseSurfaceReference : String
    distinctHiddenStatesPossible : Bool
    sameSurfaceCreatesSameObject : Bool
    hiddenAxisReference : String
    failedFactorisationMaySnowballAxis : Bool
open ProjectionCollisionPattern public

metamerCollision : ProjectionCollisionPattern
metamerCollision = projection-collision-pattern
  spectralColourDomain
  "spectral power/radiance distribution plus observer/illuminant"
  "colour-matching/tristimulus projection"
  "same observed tristimulus coordinate"
  true false
  "spectrum + observer + illuminant"
  true

braidHistoryCollision : ProjectionCollisionPattern
braidHistoryCollision = projection-collision-pattern
  braidHistoryDomain
  "literal ordered braid/crossing word"
  "fibre-count + crossing-count observation"
  "same coarse braid surface"
  true false
  "ordered crossing history / rewrite provenance"
  true

textileCraftCollision : ProjectionCollisionPattern
textileCraftCollision = projection-collision-pattern
  textileCraftDomain
  "braid/weave/knit/crochet dependency grammar"
  "common passage/loop event projection"
  "shared low-level event language"
  true false
  "craft-specific dependency and carrier topology"
  true

pantsGluingCollision : ProjectionCollisionPattern
pantsGluingCollision = projection-collision-pattern
  pantsGluingDomain
  "ternary branch/cylinder coordinates and local pants slots"
  "local branch-slot / voxel observation"
  "same local finite branching vocabulary"
  true false
  "global gluing, topology, smooth-thickening receipt"
  true

sweetgrassProvenanceCollision : ProjectionCollisionPattern
sweetgrassProvenanceCollision = projection-collision-pattern
  culturalProvenanceDomain
  "Kimmerer-attributed braid/fabric/reciprocity source role"
  "generic braid/fabric motif projection"
  "shared braid/fabric vocabulary"
  true false
  "author/source/cultural role/provenance"
  true

------------------------------------------------------------------------
-- Query-indexed consequences.
------------------------------------------------------------------------

data QueryKind : Set where
  coarseAppearanceQuery : QueryKind
  exactSpectrumQuery : QueryKind
  crossingCountQuery : QueryKind
  crossingHistoryQuery : QueryKind
  craftKindQuery : QueryKind
  gluingTopologyQuery : QueryKind
  sourceAttributionQuery : QueryKind

record QueryProjectionStatus : Set where
  constructor query-projection-status
  field
    query : QueryKind
    coarseProjectionMaySuffice : Bool
    hiddenFibreMustRemainAvailable : Bool
    projectionCollisionCanDefeatFactorisation : Bool
open QueryProjectionStatus public

appearanceStatus : QueryProjectionStatus
appearanceStatus = query-projection-status coarseAppearanceQuery true true false

spectrumStatus : QueryProjectionStatus
spectrumStatus = query-projection-status exactSpectrumQuery false true true

crossingCountStatus : QueryProjectionStatus
crossingCountStatus = query-projection-status crossingCountQuery true true false

crossingHistoryStatus : QueryProjectionStatus
crossingHistoryStatus = query-projection-status crossingHistoryQuery false true true

craftStatus : QueryProjectionStatus
craftStatus = query-projection-status craftKindQuery false true true

gluingStatus : QueryProjectionStatus
gluingStatus = query-projection-status gluingTopologyQuery false true true

attributionStatus : QueryProjectionStatus
attributionStatus = query-projection-status sourceAttributionQuery false true true

------------------------------------------------------------------------
-- Structural braid: observation compression can be useful without being
-- invertible.  Failed recovery is therefore a typed signal for a missing axis,
-- not evidence that the projection was useless for every consumer.
------------------------------------------------------------------------

record ProjectionCollisionBoundary : Set where
  constructor projection-collision-boundary
  field
    coarseQueriesMayFactorThroughProjection : Bool
    exactHistoryQueriesMayFailFactorisation : Bool
    sameVisibleOutputImpliesSameGeneratingState : Bool
    failedRecoveryCanSnowballHiddenAxis : Bool
    allPairCandidatesRemainEligible : Bool
    domainAnalogyCreatesDomainIdentity : Bool
    provenanceMayBeDroppedAfterStructuralMatch : Bool
open ProjectionCollisionBoundary public

canonicalProjectionCollisionBoundary : ProjectionCollisionBoundary
canonicalProjectionCollisionBoundary = projection-collision-boundary
  true true false true true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MetamerismEqualsTextileEquivalence : Set where
data SameClothAppearanceDeterminesWeave : Set where
data SameMCCPCellDeterminesSpectrum : Set where
data LocalPantsSlotsDetermineGlobalGluing : Set where
data SweetgrassBraidEqualsMathematicalBraid : Set where
data SharedProjectionShapeCreatesSameDomain : Set where

metamerismIsNotTextileEquivalence : MetamerismEqualsTextileEquivalence → ⊥
metamerismIsNotTextileEquivalence ()

appearanceDoesNotDetermineWeave : SameClothAppearanceDeterminesWeave → ⊥
appearanceDoesNotDetermineWeave ()

mccpDoesNotDetermineSpectrum : SameMCCPCellDeterminesSpectrum → ⊥
mccpDoesNotDetermineSpectrum ()

localPantsDoesNotDetermineGlobalGluing : LocalPantsSlotsDetermineGlobalGluing → ⊥
localPantsDoesNotDetermineGlobalGluing ()

sweetgrassBraidIsNotMathBraid : SweetgrassBraidEqualsMathematicalBraid → ⊥
sweetgrassBraidIsNotMathBraid ()

sharedShapeDoesNotIdentifyDomains : SharedProjectionShapeCreatesSameDomain → ⊥
sharedShapeDoesNotIdentifyDomains ()

------------------------------------------------------------------------
-- Exact repo-native anchors.
------------------------------------------------------------------------

projectionFibreOwner : Fibre.ProjectionFibre PC.canonicalProjectionCategory
projectionFibreOwner = Fibre.canonicalProjectionFibre

textileBoundary : Textile.TextileCrossPollinationBoundary
textileBoundary = Textile.canonicalTextileCrossPollinationBoundary

pantsBoundary : Pants.TernaryPantsGeometryBoundary
pantsBoundary = Pants.canonicalTernaryPantsGeometryBoundary

metamerBoundary : Metamer.MetamerProjectionBoundary
metamerBoundary = Metamer.canonicalMetamerProjectionBoundary

crossDomainBoundary : Cross.Ibrahim369ColourTextileBoundary
crossDomainBoundary = Cross.canonicalIbrahim369ColourTextileBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
