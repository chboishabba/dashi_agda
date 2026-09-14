module DASHI.Physics.Semiconductor.Device.LitavisSPADSpatialGranularityExact where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Physics.Semiconductor.Device.LitavisSPADMultimodalObservationExact as Litavis

------------------------------------------------------------------------
-- LITAVIS SPAD SPATIAL GRANULARITY BOUNDARY
--
-- Source-attested dimensions distinguish a 256 x 256 photon-counting surface
-- from a 64 x 64 timestamp macropixel surface.  The exact finite fixture below
-- proves only the information-theoretic boundary: if two fine spatial states
-- collide on a coarser timing surface, fine spatial identity does not factor
-- through that timing surface.  It does NOT infer a particular physical 4 x 4
-- wiring/grouping scheme from the dimension ratio alone.
------------------------------------------------------------------------

data FineSpatialState : Set where
  fineSiteA fineSiteB : FineSpatialState

data MacroTimingSite : Set where
  sameMacroTimingSite : MacroTimingSite

data FineSpatialCoordinate : Set where
  fineCoordinateA fineCoordinateB : FineSpatialCoordinate

data JoinedSpatialObservation : Set where
  joinedSpatialA joinedSpatialB : JoinedSpatialObservation

data SpatialQuery : Set where
  macroTimingIdentityQuery fineSpatialIdentityQuery : SpatialQuery

data SpatialAnswer : Set where
  macroTimingIdentityAnswer : SpatialAnswer
  fineSpatialAnswerA fineSpatialAnswerB : SpatialAnswer

macroTimingProject : FineSpatialState → MacroTimingSite
macroTimingProject fineSiteA = sameMacroTimingSite
macroTimingProject fineSiteB = sameMacroTimingSite

fineSpatialCoordinate : FineSpatialState → FineSpatialCoordinate
fineSpatialCoordinate fineSiteA = fineCoordinateA
fineSpatialCoordinate fineSiteB = fineCoordinateB

joinedSpatialProject : FineSpatialState → JoinedSpatialObservation
joinedSpatialProject fineSiteA = joinedSpatialA
joinedSpatialProject fineSiteB = joinedSpatialB

spatialAnswer : SpatialQuery → FineSpatialState → SpatialAnswer
spatialAnswer macroTimingIdentityQuery fineSiteA = macroTimingIdentityAnswer
spatialAnswer macroTimingIdentityQuery fineSiteB = macroTimingIdentityAnswer
spatialAnswer fineSpatialIdentityQuery fineSiteA = fineSpatialAnswerA
spatialAnswer fineSpatialIdentityQuery fineSiteB = fineSpatialAnswerB

spatialSemantics : Query.QuerySemantics FineSpatialState SpatialQuery SpatialAnswer
spatialSemantics = Query.querySemantics spatialAnswer

MacroTimingIdentityAdequacy : Set₁
MacroTimingIdentityAdequacy =
  Query.AdequateFor macroTimingProject spatialSemantics macroTimingIdentityQuery

FineSpatialIdentityDefect : Set₁
FineSpatialIdentityDefect =
  Query.QueryAdequacyDefect
    macroTimingProject
    spatialSemantics
    fineSpatialIdentityQuery

JoinedSpatialIdentityAdequacy : Set₁
JoinedSpatialIdentityAdequacy =
  Query.AdequateFor
    joinedSpatialProject
    spatialSemantics
    fineSpatialIdentityQuery

macroTimingIdentityAdequate : MacroTimingIdentityAdequacy
macroTimingIdentityAdequate =
  Query.factorsForQuery
    (λ observation → macroTimingIdentityAnswer)
    (λ state → refl)

fineSpatialIdentityDefect : FineSpatialIdentityDefect
fineSpatialIdentityDefect =
  Query.queryAdequacyDefect
    fineSiteA
    fineSiteB
    refl
    (λ ())

macroTimingSurfaceCannotPayFineSpatialIdentity :
  Query.AdequateFor
    macroTimingProject
    spatialSemantics
    fineSpatialIdentityQuery →
  ⊥
macroTimingSurfaceCannotPayFineSpatialIdentity =
  Query.queryAdequacyDefectBlocksFactorisation fineSpatialIdentityDefect

joinedFineSpatialAnswer : JoinedSpatialObservation → SpatialAnswer
joinedFineSpatialAnswer joinedSpatialA = fineSpatialAnswerA
joinedFineSpatialAnswer joinedSpatialB = fineSpatialAnswerB

joinedSpatialIdentityAdequate : JoinedSpatialIdentityAdequacy
joinedSpatialIdentityAdequate =
  Query.factorsForQuery joinedFineSpatialAnswer factor
  where
    factor : (state : FineSpatialState) →
      spatialAnswer fineSpatialIdentityQuery state ≡
      joinedFineSpatialAnswer (joinedSpatialProject state)
    factor fineSiteA = refl
    factor fineSiteB = refl

------------------------------------------------------------------------
-- Source-bound dimension receipt and interpretation firewall.
------------------------------------------------------------------------

record SpatialGranularityBoundary : Set where
  constructor spatial-granularity-boundary
  field
    photonCountingRows : Nat
    photonCountingColumns : Nat
    timestampMacropixelRows : Nat
    timestampMacropixelColumns : Nat
    dimensionsReuseLitavisSourceFixture : Bool
    dimensionsReuseLitavisSourceFixtureIsTrue :
      dimensionsReuseLitavisSourceFixture ≡ true
    differentGridDimensionsImplyIdenticalSpatialInformation : Bool
    differentGridDimensionsImplyIdenticalSpatialInformationIsFalse :
      differentGridDimensionsImplyIdenticalSpatialInformation ≡ false
    dimensionRatioAloneProvesPhysicalFourByFourGrouping : Bool
    dimensionRatioAloneProvesPhysicalFourByFourGroupingIsFalse :
      dimensionRatioAloneProvesPhysicalFourByFourGrouping ≡ false
    coarserTimingSurfaceCanLoseFineSpatialIdentity : Bool
    coarserTimingSurfaceCanLoseFineSpatialIdentityIsTrue :
      coarserTimingSurfaceCanLoseFineSpatialIdentity ≡ true
    joinedObserverCanRepairDeclaredFineIdentityQuery : Bool
    joinedObserverCanRepairDeclaredFineIdentityQueryIsTrue :
      joinedObserverCanRepairDeclaredFineIdentityQuery ≡ true
    sourceClaimCreatesThisNonfactorabilityProof : Bool
    sourceClaimCreatesThisNonfactorabilityProofIsFalse :
      sourceClaimCreatesThisNonfactorabilityProof ≡ false

canonicalSpatialGranularityBoundary : SpatialGranularityBoundary
canonicalSpatialGranularityBoundary =
  spatial-granularity-boundary
    (Litavis.photonCountingRows Litavis.litavisSourceAttestedArchitecture)
    (Litavis.photonCountingColumns Litavis.litavisSourceAttestedArchitecture)
    (Litavis.timestampMacropixelRows Litavis.litavisSourceAttestedArchitecture)
    (Litavis.timestampMacropixelColumns Litavis.litavisSourceAttestedArchitecture)
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
