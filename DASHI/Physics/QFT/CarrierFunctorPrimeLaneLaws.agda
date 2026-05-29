module DASHI.Physics.QFT.CarrierFunctorPrimeLaneLaws where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierToPhysicsInterpretationFunctor as CarrierFunctor
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Moonshine
import DASHI.Physics.Closure.PrimeLaneGaugeAssignmentReceiptSurface as LaneGauge
import DASHI.Physics.QFT.CarrierFunctorResidualInstances as Residual
import DASHI.Physics.QFT.DHRSectorFunctoriality as DHRSector
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import MonsterOntos as MO
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI

------------------------------------------------------------------------
-- Chain A1 prime-lane functor laws.
--
-- This QFT-owned surface packages only the concrete prime-lane functor
-- laws already present in the carrier layer.  The inhabited part is bounded
-- to p2, p3, p5, and p7, and the FactorVec covariance law is consumed from
-- the concrete prime-bump commutation theorem.  DHR-sector compatibility and
-- exact Standard Model matching remain fail-closed through the existing
-- residual receipts.

data ChainA1PrimeLane : Set where
  a1-p2 :
    ChainA1PrimeLane

  a1-p3 :
    ChainA1PrimeLane

  a1-p5 :
    ChainA1PrimeLane

  a1-p7 :
    ChainA1PrimeLane

chainA1PrimeLaneToMonster :
  ChainA1PrimeLane →
  Moonshine.MonsterPrimeLane
chainA1PrimeLaneToMonster a1-p2 =
  Moonshine.p2
chainA1PrimeLaneToMonster a1-p3 =
  Moonshine.p3
chainA1PrimeLaneToMonster a1-p5 =
  Moonshine.p5
chainA1PrimeLaneToMonster a1-p7 =
  Moonshine.p7

chainA1PrimeLaneToGaugeFactor :
  ChainA1PrimeLane →
  LaneGauge.E8McKayLaneGaugeFactor
chainA1PrimeLaneToGaugeFactor a1-p2 =
  LaneGauge.e8LaneU1Y
chainA1PrimeLaneToGaugeFactor a1-p3 =
  LaneGauge.e8LaneSU2L
chainA1PrimeLaneToGaugeFactor a1-p5 =
  LaneGauge.e8LaneSU3c
chainA1PrimeLaneToGaugeFactor a1-p7 =
  LaneGauge.e8LaneSU2RBrokenAtSeesaw

chainA1PrimeLaneToSSP :
  ChainA1PrimeLane →
  MO.SSP
chainA1PrimeLaneToSSP lane =
  CarrierFunctor.monsterPrimeLaneToSSP
    (chainA1PrimeLaneToMonster lane)

chainA1ObjectLaw :
  (lane : ChainA1PrimeLane) →
  CarrierFunctor.carrierToPhysicsObjectMap
    (CarrierFunctor.primeLaneCarrierObject
      (chainA1PrimeLaneToMonster lane))
  ≡
  CarrierFunctor.gaugeLaneRepresentationObject
    (chainA1PrimeLaneToGaugeFactor lane)
chainA1ObjectLaw a1-p2 =
  refl
chainA1ObjectLaw a1-p3 =
  refl
chainA1ObjectLaw a1-p5 =
  refl
chainA1ObjectLaw a1-p7 =
  refl

chainA1PrimeBumpMorphismLaw :
  (lane : ChainA1PrimeLane) →
  CarrierFunctor.carrierToPhysicsMorphismMap
    (CarrierFunctor.primeBumpShift
      (chainA1PrimeLaneToMonster lane))
  ≡
  CarrierFunctor.gaugeCovariantPrimeShift
    (chainA1PrimeLaneToMonster lane)
chainA1PrimeBumpMorphismLaw lane =
  CarrierFunctor.carrierToPhysicsPrimeBumpNaturality
    (chainA1PrimeLaneToMonster lane)

chainA1LaneInclusionMorphismLaw :
  (lane : ChainA1PrimeLane) →
  CarrierFunctor.carrierToPhysicsMorphismMap
    (CarrierFunctor.laneToProductInclusion
      (chainA1PrimeLaneToMonster lane))
  ≡
  CarrierFunctor.gaugeLaneToProductInclusion
    (chainA1PrimeLaneToMonster lane)
chainA1LaneInclusionMorphismLaw lane =
  CarrierFunctor.carrierToPhysicsLaneInclusionNaturality
    (chainA1PrimeLaneToMonster lane)

chainA1FactorVecPrimeBumpCovariance :
  (left right : ChainA1PrimeLane) →
  (carrier : GL.FactorVec) →
  FVI.primeBump
    (chainA1PrimeLaneToSSP left)
    (FVI.primeBump (chainA1PrimeLaneToSSP right) carrier)
  ≡
  FVI.primeBump
    (chainA1PrimeLaneToSSP right)
    (FVI.primeBump (chainA1PrimeLaneToSSP left) carrier)
chainA1FactorVecPrimeBumpCovariance left right carrier =
  FVI.primeBumpCommutes
    (chainA1PrimeLaneToSSP left)
    (chainA1PrimeLaneToSSP right)
    carrier

record ChainA1PrimeLaneFunctorLawRow
  (lane : ChainA1PrimeLane) :
  Setω where
  field
    monsterLane :
      Moonshine.MonsterPrimeLane

    monsterLaneIsCanonical :
      monsterLane ≡ chainA1PrimeLaneToMonster lane

    gaugeFactor :
      LaneGauge.E8McKayLaneGaugeFactor

    gaugeFactorIsCanonical :
      gaugeFactor ≡ chainA1PrimeLaneToGaugeFactor lane

    objectLaw :
      CarrierFunctor.carrierToPhysicsObjectMap
        (CarrierFunctor.primeLaneCarrierObject monsterLane)
      ≡
      CarrierFunctor.gaugeLaneRepresentationObject gaugeFactor

    primeBumpMorphismLaw :
      CarrierFunctor.carrierToPhysicsMorphismMap
        (CarrierFunctor.primeBumpShift monsterLane)
      ≡
      CarrierFunctor.gaugeCovariantPrimeShift monsterLane

    laneInclusionMorphismLaw :
      CarrierFunctor.carrierToPhysicsMorphismMap
        (CarrierFunctor.laneToProductInclusion monsterLane)
      ≡
      CarrierFunctor.gaugeLaneToProductInclusion monsterLane

open ChainA1PrimeLaneFunctorLawRow public

chainA1PrimeLaneFunctorLawRow :
  (lane : ChainA1PrimeLane) →
  ChainA1PrimeLaneFunctorLawRow lane
chainA1PrimeLaneFunctorLawRow a1-p2 =
  record
    { monsterLane =
        Moonshine.p2
    ; monsterLaneIsCanonical =
        refl
    ; gaugeFactor =
        LaneGauge.e8LaneU1Y
    ; gaugeFactorIsCanonical =
        refl
    ; objectLaw =
        refl
    ; primeBumpMorphismLaw =
        CarrierFunctor.carrierToPhysicsPrimeBumpNaturality Moonshine.p2
    ; laneInclusionMorphismLaw =
        CarrierFunctor.carrierToPhysicsLaneInclusionNaturality Moonshine.p2
    }
chainA1PrimeLaneFunctorLawRow a1-p3 =
  record
    { monsterLane =
        Moonshine.p3
    ; monsterLaneIsCanonical =
        refl
    ; gaugeFactor =
        LaneGauge.e8LaneSU2L
    ; gaugeFactorIsCanonical =
        refl
    ; objectLaw =
        refl
    ; primeBumpMorphismLaw =
        CarrierFunctor.carrierToPhysicsPrimeBumpNaturality Moonshine.p3
    ; laneInclusionMorphismLaw =
        CarrierFunctor.carrierToPhysicsLaneInclusionNaturality Moonshine.p3
    }
chainA1PrimeLaneFunctorLawRow a1-p5 =
  record
    { monsterLane =
        Moonshine.p5
    ; monsterLaneIsCanonical =
        refl
    ; gaugeFactor =
        LaneGauge.e8LaneSU3c
    ; gaugeFactorIsCanonical =
        refl
    ; objectLaw =
        refl
    ; primeBumpMorphismLaw =
        CarrierFunctor.carrierToPhysicsPrimeBumpNaturality Moonshine.p5
    ; laneInclusionMorphismLaw =
        CarrierFunctor.carrierToPhysicsLaneInclusionNaturality Moonshine.p5
    }
chainA1PrimeLaneFunctorLawRow a1-p7 =
  record
    { monsterLane =
        Moonshine.p7
    ; monsterLaneIsCanonical =
        refl
    ; gaugeFactor =
        LaneGauge.e8LaneSU2RBrokenAtSeesaw
    ; gaugeFactorIsCanonical =
        refl
    ; objectLaw =
        refl
    ; primeBumpMorphismLaw =
        CarrierFunctor.carrierToPhysicsPrimeBumpNaturality Moonshine.p7
    ; laneInclusionMorphismLaw =
        CarrierFunctor.carrierToPhysicsLaneInclusionNaturality Moonshine.p7
    }

record ChainA1PrimeLaneFunctorLaws : Setω₅ where
  field
    carrierGraphFunctor :
      CarrierFunctor.CarrierToPhysicsGraphFunctor

    carrierFunctorLawSurface :
      CarrierFunctor.CarrierToPhysicsFunctorLawReceiptSurface

    residualWitnessBundle :
      Residual.Gate1ResidualUpstreamWitnessBundle

    dhrSectorFunctorialityBoundary :
      DHRSector.DHRSectorFunctorialityReceipt

    exactSMBlockerReceipt :
      ExactSM.ExactSMMatchBlockerReceipt

    p2LawRow :
      ChainA1PrimeLaneFunctorLawRow a1-p2

    p3LawRow :
      ChainA1PrimeLaneFunctorLawRow a1-p3

    p5LawRow :
      ChainA1PrimeLaneFunctorLawRow a1-p5

    p7LawRow :
      ChainA1PrimeLaneFunctorLawRow a1-p7

    identityPreserved :
      (x : CarrierFunctor.DASHICarrierObject) →
      CarrierFunctor.carrierToPhysicsMorphismMap
        (CarrierFunctor.carrierIdentity x)
      ≡
      CarrierFunctor.physIdentity
        (CarrierFunctor.carrierToPhysicsObjectMap x)

    compositionPreserved :
      {x y z : CarrierFunctor.DASHICarrierObject} →
      (f : CarrierFunctor.DASHICarrierMorphism x y) →
      (g : CarrierFunctor.DASHICarrierMorphism y z) →
      CarrierFunctor.carrierToPhysicsMorphismMap
        (CarrierFunctor.carrierCompose g f)
      ≡
      CarrierFunctor.physCompose
        (CarrierFunctor.carrierToPhysicsMorphismMap g)
        (CarrierFunctor.carrierToPhysicsMorphismMap f)

    p2p3FactorVecCovariance :
      (carrier : GL.FactorVec) →
      chainA1FactorVecPrimeBumpCovariance a1-p2 a1-p3 carrier
      ≡
      FVI.primeBumpCommutes MO.p2 MO.p3 carrier

    p2p5FactorVecCovariance :
      (carrier : GL.FactorVec) →
      chainA1FactorVecPrimeBumpCovariance a1-p2 a1-p5 carrier
      ≡
      FVI.primeBumpCommutes MO.p2 MO.p5 carrier

    p3p5FactorVecCovariance :
      (carrier : GL.FactorVec) →
      chainA1FactorVecPrimeBumpCovariance a1-p3 a1-p5 carrier
      ≡
      FVI.primeBumpCommutes MO.p3 MO.p5 carrier

    p5p7FactorVecCovariance :
      (carrier : GL.FactorVec) →
      chainA1FactorVecPrimeBumpCovariance a1-p5 a1-p7 carrier
      ≡
      FVI.primeBumpCommutes MO.p5 MO.p7 carrier

    a1PrimeLaneFunctorLawsInhabited :
      Bool

    a1PrimeLaneFunctorLawsInhabitedIsTrue :
      a1PrimeLaneFunctorLawsInhabited ≡ true

    dhrSectorCompatibilityPromoted :
      Bool

    dhrSectorCompatibilityPromotedIsFalse :
      dhrSectorCompatibilityPromoted ≡ false

    exactSMMatchPromoted :
      Bool

    exactSMMatchPromotedIsFalse :
      exactSMMatchPromoted ≡ false

    boundary :
      List String

open ChainA1PrimeLaneFunctorLaws public

canonicalChainA1PrimeLaneFunctorLaws :
  ChainA1PrimeLaneFunctorLaws
canonicalChainA1PrimeLaneFunctorLaws =
  record
    { carrierGraphFunctor =
        CarrierFunctor.canonicalCarrierToPhysicsGraphFunctor
    ; carrierFunctorLawSurface =
        CarrierFunctor.canonicalCarrierToPhysicsFunctorLawReceiptSurface
    ; residualWitnessBundle =
        Residual.canonicalGate1ResidualUpstreamWitnessBundle
    ; dhrSectorFunctorialityBoundary =
        DHRSector.canonicalDHRSectorFunctorialityReceipt
    ; exactSMBlockerReceipt =
        ExactSM.canonicalExactSMMatchBlockerReceipt
    ; p2LawRow =
        chainA1PrimeLaneFunctorLawRow a1-p2
    ; p3LawRow =
        chainA1PrimeLaneFunctorLawRow a1-p3
    ; p5LawRow =
        chainA1PrimeLaneFunctorLawRow a1-p5
    ; p7LawRow =
        chainA1PrimeLaneFunctorLawRow a1-p7
    ; identityPreserved =
        CarrierFunctor.carrierToPhysicsPreservesIdentity
    ; compositionPreserved =
        CarrierFunctor.carrierToPhysicsPreservesComposition
    ; p2p3FactorVecCovariance =
        λ carrier → refl
    ; p2p5FactorVecCovariance =
        λ carrier → refl
    ; p3p5FactorVecCovariance =
        λ carrier → refl
    ; p5p7FactorVecCovariance =
        λ carrier → refl
    ; a1PrimeLaneFunctorLawsInhabited =
        true
    ; a1PrimeLaneFunctorLawsInhabitedIsTrue =
        refl
    ; dhrSectorCompatibilityPromoted =
        false
    ; dhrSectorCompatibilityPromotedIsFalse =
        refl
    ; exactSMMatchPromoted =
        false
    ; exactSMMatchPromotedIsFalse =
        refl
    ; boundary =
        "A1 is inhabited only for the bounded p2, p3, p5, and p7 prime-lane functor laws"
        ∷ "Object, prime-bump morphism, lane-inclusion morphism, identity, and composition laws reduce through the carrier graph functor surface"
        ∷ "FactorVec prime-bump covariance is consumed from Ontology.Hecke.FactorVecInstances.primeBumpCommutes"
        ∷ "DHR-sector compatibility remains the existing missingDHRSectorCompatibility residual"
        ∷ "Exact Standard Model matching remains fail-closed through canonicalExactSMMatchBlockerReceipt"
        ∷ []
    }

chainA1PrimeLaneFunctorLawsStatus :
  Bool
chainA1PrimeLaneFunctorLawsStatus =
  a1PrimeLaneFunctorLawsInhabited
    canonicalChainA1PrimeLaneFunctorLaws
