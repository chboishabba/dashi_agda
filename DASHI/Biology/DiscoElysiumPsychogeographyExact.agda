module DASHI.Biology.DiscoElysiumPsychogeographyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.PsychogeographicFieldExact as Field

------------------------------------------------------------------------
-- Fictional design source: ZA/UM, Disco Elysium (2019), no DOI assigned.
--
-- This module extracts finite structural mechanisms from the work: collective
-- spatial obstruction, information/provenance cross-talk, a locally small but
-- relationally large singularity, and clue-indexed forced derive.  These are
-- fictional/formal inspirations, not empirical claims about real cities.
------------------------------------------------------------------------

data ObstructionLayer : Set where
  personalLayer : ObstructionLayer
  familyLayer : ObstructionLayer
  classLayer : ObstructionLayer
  institutionalLayer : ObstructionLayer
  historicalLayer : ObstructionLayer

martinaiseObstructionProfile : List ObstructionLayer
martinaiseObstructionProfile =
  personalLayer ∷ familyLayer ∷ classLayer ∷ institutionalLayer ∷ historicalLayer ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

martinaiseProfileHasFiveDistinctScales :
  listCount martinaiseObstructionProfile ≡ 5
martinaiseProfileHasFiveDistinctScales = refl

data MemoryContent : Set where
  harbourStrikeContent : MemoryContent
  lostRelationshipContent : MemoryContent
  anonymousBroadcastContent : MemoryContent

data ProvenanceStrength : Set where
  strongProvenance : ProvenanceStrength
  weakProvenance : ProvenanceStrength
  absentProvenance : ProvenanceStrength

record InformationTrace : Set where
  constructor informationTrace
  field
    content : MemoryContent
    provenanceStrength : ProvenanceStrength
    temporalIndex : Nat
    spatialIndex : Nat

open InformationTrace public

stableTrace : InformationTrace
stableTrace = informationTrace harbourStrikeContent strongProvenance 7 4

paleCrossTalk : InformationTrace → InformationTrace
paleCrossTalk trace =
  informationTrace
    (content trace)
    weakProvenance
    0
    0

crossTalkPreservesContentWhileWeakeningProvenance :
  content (paleCrossTalk stableTrace) ≡ content stableTrace
  × provenanceStrength (paleCrossTalk stableTrace) ≡ weakProvenance
crossTalkPreservesContentWhileWeakeningProvenance = refl , refl

crossTalkDoesNotPreserveStrongProvenance :
  ¬ (provenanceStrength (paleCrossTalk stableTrace)
     ≡ provenanceStrength stableTrace)
crossTalkDoesNotPreserveStrongProvenance ()

------------------------------------------------------------------------
-- A local singularity may be geometrically small but relationally dominant.
------------------------------------------------------------------------

record LocalUrbanSingularity : Set where
  constructor localUrbanSingularity
  field
    singularityLabel : String
    geometricSize : Nat
    relationalEffect : Nat
    surroundingSite : Field.Site

open LocalUrbanSingularity public

twoMillimetreHole : LocalUrbanSingularity
twoMillimetreHole =
  localUrbanSingularity "two-millimetre hole" 2 9 Field.churchSite

tinyCarrierLargeEffectWitness :
  geometricSize twoMillimetreHole ≡ 2
  × relationalEffect twoMillimetreHole ≡ 9
tinyCarrierLargeEffectWitness = refl , refl

------------------------------------------------------------------------
-- Returning to one physical site need not return the walker to one state.
------------------------------------------------------------------------

data LoopState : Set where
  beforeLoop : LoopState
  afterLoop : LoopState

loopEndpoint : LoopState → Field.Site
loopEndpoint beforeLoop = Field.churchSite
loopEndpoint afterLoop = Field.churchSite

loopReturnsToSameSite : loopEndpoint beforeLoop ≡ loopEndpoint afterLoop
loopReturnsToSameSite = refl

loopRetainsNontrivialResidual : ¬ (beforeLoop ≡ afterLoop)
loopRetainsNontrivialResidual ()

------------------------------------------------------------------------
-- Detective case as a clue-constrained derive.
------------------------------------------------------------------------

data CaseStage : Set where
  noClueStage : CaseStage
  bodyClueStage : CaseStage
  harbourClueStage : CaseStage
  islandRouteStage : CaseStage

data CaseRoute : Set where
  yardRoute : CaseRoute
  harbourRoute : CaseRoute
  islandRoute : CaseRoute
  noRoute : CaseRoute

availableRoute : CaseStage → CaseRoute
availableRoute noClueStage = yardRoute
availableRoute bodyClueStage = harbourRoute
availableRoute harbourClueStage = islandRoute
availableRoute islandRouteStage = islandRoute

harbourClueOpensIslandRoute :
  availableRoute harbourClueStage ≡ islandRoute
harbourClueOpensIslandRoute = refl

noClueDoesNotAlreadyOpenIsland :
  ¬ (availableRoute noClueStage ≡ islandRoute)
noClueDoesNotAlreadyOpenIsland ()

record DiscoPsychogeographyBoundary : Set where
  constructor discoPsychogeographyBoundary
  field
    personalPsycheEqualsDistrict : Bool
    personalPsycheEqualsDistrictIsFalse : personalPsycheEqualsDistrict ≡ false
    vividContentGuaranteesSourceAccuracy : Bool
    vividContentGuaranteesSourceAccuracyIsFalse :
      vividContentGuaranteesSourceAccuracy ≡ false
    fictionalPaleIsRealPhysicalTheory : Bool
    fictionalPaleIsRealPhysicalTheoryIsFalse :
      fictionalPaleIsRealPhysicalTheory ≡ false
    smallGeometryImpliesSmallRelationalEffect : Bool
    smallGeometryImpliesSmallRelationalEffectIsFalse :
      smallGeometryImpliesSmallRelationalEffect ≡ false

canonicalDiscoPsychogeographyBoundary : DiscoPsychogeographyBoundary
canonicalDiscoPsychogeographyBoundary =
  discoPsychogeographyBoundary false refl false refl false refl false refl
