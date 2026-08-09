module DASHI.Topology.HelicalWeaveMappingTorusExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Circular fabric topology and helical production trajectory are distinct.
-- The finite mapping-torus presentation below carries an order-three
-- monodromy: each production step advances the round and rotates the phase;
-- three steps return to the same phase but not to the same production round.
------------------------------------------------------------------------

data Phase3 : Set where
  phase0 phase1 phase2 : Phase3

rotatePhase : Phase3 → Phase3
rotatePhase phase0 = phase1
rotatePhase phase1 = phase2
rotatePhase phase2 = phase0

rotatePhaseTwice : Phase3 → Phase3
rotatePhaseTwice phase = rotatePhase (rotatePhase phase)

rotatePhaseThreeTimes : Phase3 → Phase3
rotatePhaseThreeTimes phase = rotatePhase (rotatePhaseTwice phase)

rotationHasOrderThree :
  (phase : Phase3) →
  rotatePhaseThreeTimes phase ≡ phase
rotationHasOrderThree phase0 = refl
rotationHasOrderThree phase1 = refl
rotationHasOrderThree phase2 = refl

rotationIsNontrivialAtPhaseZero :
  rotatePhase phase0 ≡ phase0 → ⊥
rotationIsNontrivialAtPhaseZero ()

record HelicalSite : Set where
  constructor helicalSite
  field
    productionRound : Nat
    stitchPhase : Phase3

open HelicalSite public

helicalStep : HelicalSite → HelicalSite
helicalStep (helicalSite round phase) =
  helicalSite (suc round) (rotatePhase phase)

helicalThreeSteps : HelicalSite → HelicalSite
helicalThreeSteps site =
  helicalStep (helicalStep (helicalStep site))

threeStepsReturnToSamePhase :
  (site : HelicalSite) →
  stitchPhase (helicalThreeSteps site) ≡ stitchPhase site
threeStepsReturnToSamePhase (helicalSite round phase) =
  rotationHasOrderThree phase

threeStepsAdvanceProductionRound :
  (site : HelicalSite) →
  productionRound (helicalThreeSteps site)
  ≡ 3 + productionRound site
threeStepsAdvanceProductionRound (helicalSite round phase) = refl

data FabricTopology : Set where
  flatRectangle : FabricTopology
  cylindricalFabric : FabricTopology
  toroidalClosure : FabricTopology

data ProductionTrajectory : Set where
  rowByRow : ProductionTrajectory
  helicalTrajectory : ProductionTrajectory

record CircularWeaveGeometry : Set₁ where
  constructor circularWeaveGeometry
  field
    topology : FabricTopology
    trajectory : ProductionTrajectory
    phaseCarrier : Set
    monodromy : phaseCarrier → phaseCarrier
    monodromyPeriod : Nat
    iterateMonodromy : Nat → phaseCarrier → phaseCarrier
    periodLaw :
      (phase : phaseCarrier) →
      iterateMonodromy monodromyPeriod phase ≡ phase

open CircularWeaveGeometry public

iterateRotation : Nat → Phase3 → Phase3
iterateRotation zero phase = phase
iterateRotation (suc n) phase =
  iterateRotation n (rotatePhase phase)

iterateRotationThree :
  (phase : Phase3) →
  iterateRotation 3 phase ≡ phase
iterateRotationThree phase0 = refl
iterateRotationThree phase1 = refl
iterateRotationThree phase2 = refl

canonicalHelicalCylinder : CircularWeaveGeometry
canonicalHelicalCylinder =
  circularWeaveGeometry
    cylindricalFabric
    helicalTrajectory
    Phase3
    rotatePhase
    3
    iterateRotation
    iterateRotationThree

------------------------------------------------------------------------
-- The three phases are a finite monodromy carrier.  Identifying them with
-- physical particle generations requires an additional equivariant map and
-- is not implied by order-three closure alone.
------------------------------------------------------------------------

record HelicalGenerationBoundary : Set where
  constructor helicalGenerationBoundary
  field
    fabricTopologyIsCylinder :
      topology canonicalHelicalCylinder ≡ cylindricalFabric
    productionPathIsHelical :
      trajectory canonicalHelicalCylinder ≡ helicalTrajectory
    monodromyClosesAfterThree :
      (phase : Phase3) → iterateRotation 3 phase ≡ phase
    orderThreeMonodromyIsPhysicalGenerationAssignment : Bool
    orderThreeMonodromyIsPhysicalGenerationAssignmentIsFalse :
      orderThreeMonodromyIsPhysicalGenerationAssignment ≡ false
    finitePresentationConstructsTopologicalQuotient : Bool
    finitePresentationConstructsTopologicalQuotientIsFalse :
      finitePresentationConstructsTopologicalQuotient ≡ false

canonicalHelicalGenerationBoundary : HelicalGenerationBoundary
canonicalHelicalGenerationBoundary =
  helicalGenerationBoundary
    refl
    refl
    iterateRotationThree
    false refl
    false refl
