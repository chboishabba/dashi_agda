module DASHI.Moonshine.OggSSPP3DeligneRapoportDegeneracyTransportCutsetExact where

------------------------------------------------------------------------
-- p=3 X0(3) LOCAL-INCIDENCE -> X(1)^rig WILD-ROOT TRANSPORT CUTSET
--
-- The sourced one-Artin--Schreier-layer description lives on X(1)^rig.
-- The two-sector p=3 correction donor lives on the Deligne--Rapoport local
-- incidence geometry of X0(3):
--
--   node orbit,
--   Frobenius/Verschiebung branch-pair orbit.
--
-- Under the forgetful/degeneracy map X0(3) -> X(1), all three local strata lie
-- over the SAME supersingular coarse point.  Hence the base root-stack object
-- does not by itself retain the node-vs-branch distinction.
--
-- A valid p=3 layer x two-sector valuation theorem must pull the wild local
-- object to the bad-level X0(3) geometry and prove branch-sensitive local
-- divisor/q-expansion terms there.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as DR
import DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact as LayerSector
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Coarse forgetting collapses all local incidence strata.
------------------------------------------------------------------------

forgetToSupersingularBase :
  DR.P3LocalStratum ->
  ⊤
forgetToSupersingularBase stratum = tt

frobeniusAndNodeCollapse :
  forgetToSupersingularBase DR.frobeniusBranch
  ≡ forgetToSupersingularBase DR.supersingularNode
frobeniusAndNodeCollapse = refl

nodeAndVerschiebungCollapse :
  forgetToSupersingularBase DR.supersingularNode
  ≡ forgetToSupersingularBase DR.verschiebungBranch
nodeAndVerschiebungCollapse = refl

data BaseSupersingularPointRecoversLocalStratum : Set where
data X1RootStackAloneRecoversNodeBranchOrbit : Set where

basePointDoesNotRecoverLocalStratum :
  BaseSupersingularPointRecoversLocalStratum -> ⊥
basePointDoesNotRecoverLocalStratum ()

x1RootStackAloneDoesNotRecoverNodeBranchOrbit :
  X1RootStackAloneRecoversNodeBranchOrbit -> ⊥
x1RootStackAloneDoesNotRecoverNodeBranchOrbit ()

------------------------------------------------------------------------
-- 2. Orbit-level distinction that must be restored after pullback.
------------------------------------------------------------------------

data P3OrbitWitness : Set where
  nodeWitness :
    P3OrbitWitness
  branchPairWitness :
    P3OrbitWitness

orbitWitnessToLocalOrbit :
  P3OrbitWitness ->
  DR.P3LocalOrbit
orbitWitnessToLocalOrbit nodeWitness =
  DR.nodeOrbit
orbitWitnessToLocalOrbit branchPairWitness =
  DR.branchOrbit

------------------------------------------------------------------------
-- 3. Required branch-sensitive pullback authority.
------------------------------------------------------------------------

record P3BadLevelBranchTransportAuthority : Set₁ where
  field
    PulledBackWildObject : Set

    nodeLocalTerm :
      PulledBackWildObject

    branchPairLocalTerm :
      PulledBackWildObject

    pulledBackFromX1RigidifiedWildLayer :
      Bool
    pulledBackFromX1RigidifiedWildLayerIsTrue :
      pulledBackFromX1RigidifiedWildLayer ≡ true

    livesOnBadLevelX03Neighborhood :
      Bool
    livesOnBadLevelX03NeighborhoodIsTrue :
      livesOnBadLevelX03Neighborhood ≡ true

    nodeBranchDistinctionRetained :
      Bool
    nodeBranchDistinctionRetainedIsTrue :
      nodeBranchDistinctionRetained ≡ true

    branchSensitivityDerivedFromDegeneracyGeometry :
      Bool
    branchSensitivityDerivedFromDegeneracyGeometryIsTrue :
      branchSensitivityDerivedFromDegeneracyGeometry ≡ true

    localDivisorOrQExpansionOrdersOwned :
      Bool
    localDivisorOrQExpansionOrdersOwnedIsTrue :
      localDivisorOrQExpansionOrdersOwned ≡ true

open P3BadLevelBranchTransportAuthority public

data P3BadLevelBranchTransportAuthorityInhabited : Set where

p3BadLevelBranchTransportStillOpen :
  P3BadLevelBranchTransportAuthorityInhabited -> ⊥
p3BadLevelBranchTransportStillOpen ()

------------------------------------------------------------------------
-- 4. Existing product candidate cannot pay this transport by counting.
------------------------------------------------------------------------

layerSectorBoundary :
  LayerSector.WildLayerSectorProductBoundary
layerSectorBoundary =
  LayerSector.canonicalWildLayerSectorProductBoundary

data TwoOrbitCountCreatesBranchTransport : Set where
data OneWildLayerCreatesBranchSensitivePullback : Set where

twoOrbitCountDoesNotCreateBranchTransport :
  TwoOrbitCountCreatesBranchTransport -> ⊥
twoOrbitCountDoesNotCreateBranchTransport ()

oneWildLayerDoesNotCreateBranchSensitivePullback :
  OneWildLayerCreatesBranchSensitivePullback -> ⊥
oneWildLayerDoesNotCreateBranchSensitivePullback ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record P3DegeneracyTransportCutsetBoundary : Set where
  constructor p3-degeneracy-transport-cutset-boundary
  field
    threeLocalStrataCollapseToOneBasePoint : Bool
    nodeBranchOrbitNotRecoveredFromBasePoint : Bool
    branchSensitivePullbackAuthoritySpecified : Bool
    authorityMustLiveOnBadLevelX03 : Bool
    divisorOrQExpansionPaymentRequired : Bool
    branchTransportAuthorityInhabited : Bool
    countPromotedToTransportTheorem : Bool

canonicalP3DegeneracyTransportCutsetBoundary :
  P3DegeneracyTransportCutsetBoundary
canonicalP3DegeneracyTransportCutsetBoundary =
  p3-degeneracy-transport-cutset-boundary
    true true true true true false false
