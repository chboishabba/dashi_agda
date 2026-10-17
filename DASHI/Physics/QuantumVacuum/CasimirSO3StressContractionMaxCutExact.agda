module DASHI.Physics.QuantumVacuum.CasimirSO3StressContractionMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.RecursiveRadixHypervoxel as HyperBase
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3
import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque
import DASHI.Physics.QuantumVacuum.BrownMaclayParallelPlateSourceAuthorityExact as BrownMaclay
import DASHI.Physics.QuantumVacuum.Casimir369HyperfabricCommutationExact as Casimir369

------------------------------------------------------------------------
-- CASIMIR SPATIAL STRESS x SO(3) 9-SHEET MAX-CUT
--
-- Recent torque work makes the physically meaningful role of the repository's
-- SO(3) operator sheet sharper.  The 9-sheet is an ordered spatial rank-two
-- carrier: output axis x input axis.  For parallel plates, a spatial stress
-- tensor therefore lives naturally on exactly that carrier.
--
-- For a chosen orthonormal plate frame
--
--   tangent-1, tangent-2, normal,
--
-- contraction of the stress tensor with the basis normal is simply selection
-- of the normal input column:
--
--   T_ij n_j  ->  T_i,n                         (9 -> 3)
--
-- and the normal pressure is the second contraction
--
--   n_i T_ij n_j  ->  T_n,n.                   (3 -> 1)
--
-- This is a genuine same-carrier tensor-contraction interpretation of 9 -> 3
-- -> 1.  It does NOT say that the numerical factor three in
--
--   720 -> 240
--
-- is caused by the 9 -> 3 carrier reduction.  The Casimir derivative route
-- owns its own inverse-cube differentiation semantics; cardinality is not a
-- derivative theorem.
--
-- It also corrects a possible overreading of the earlier finite mode-family
-- chart: TEM/TE/TM are mode-family coordinates, not physical spatial axes.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. A chosen parallel-plate spatial frame on the existing three-axis carrier.
------------------------------------------------------------------------

data PlateDirection : Set where
  tangentOne tangentTwo normal : PlateDirection

plateDirectionToAxis : PlateDirection → SO3.SU2Axis
plateDirectionToAxis tangentOne = SO3.axis₁
plateDirectionToAxis tangentTwo = SO3.axis₂
plateDirectionToAxis normal = SO3.axis₃

axisToPlateDirection : SO3.SU2Axis → PlateDirection
axisToPlateDirection HyperBase.axis-low = tangentOne
axisToPlateDirection HyperBase.axis-mid = tangentTwo
axisToPlateDirection HyperBase.axis-high = normal

plateDirectionAxisRoundTrip :
  ∀ direction →
  axisToPlateDirection (plateDirectionToAxis direction) ≡ direction
plateDirectionAxisRoundTrip tangentOne = refl
plateDirectionAxisRoundTrip tangentTwo = refl
plateDirectionAxisRoundTrip normal = refl

axisPlateDirectionRoundTrip :
  ∀ axis →
  plateDirectionToAxis (axisToPlateDirection axis) ≡ axis
axisPlateDirectionRoundTrip HyperBase.axis-low = refl
axisPlateDirectionRoundTrip HyperBase.axis-mid = refl
axisPlateDirectionRoundTrip HyperBase.axis-high = refl

plateTangentOneAxis plateTangentTwoAxis plateNormalAxis : SO3.SU2Axis
plateTangentOneAxis = plateDirectionToAxis tangentOne
plateTangentTwoAxis = plateDirectionToAxis tangentTwo
plateNormalAxis = plateDirectionToAxis normal

------------------------------------------------------------------------
-- 2. Spatial stress tensor on the literal repository 3 x 3 operator sheet.
------------------------------------------------------------------------

SpatialStressSheet : Set → Set
SpatialStressSheet Value = SO3.OperatorSheet Value

normalColumnSlot : SO3.SU2Axis → SO3.MatrixSlot
normalColumnSlot output = output , plateNormalAxis

tractionAgainstPlateNormal :
  ∀ {Value : Set} →
  SpatialStressSheet Value →
  SO3.SU2Axis →
  Value
tractionAgainstPlateNormal stress output =
  stress (normalColumnSlot output)

normalPressure :
  ∀ {Value : Set} →
  SpatialStressSheet Value →
  Value
normalPressure stress =
  tractionAgainstPlateNormal stress plateNormalAxis

normalPressureViaTraction :
  ∀ {Value : Set} →
  (stress : SpatialStressSheet Value) →
  normalPressure stress
  ≡ tractionAgainstPlateNormal stress plateNormalAxis
normalPressureViaTraction stress = refl

normalPressureIsNormalNormalComponent :
  ∀ {Value : Set} →
  (stress : SpatialStressSheet Value) →
  normalPressure stress
  ≡ stress (plateNormalAxis , plateNormalAxis)
normalPressureIsNormalNormalComponent stress = refl

------------------------------------------------------------------------
-- 3. Same operator-sheet carrier as the torque PR, but different semantics.
--
-- Torque #1164 reads a MatrixSlot as ordered (lever axis, force axis) inside a
-- three-axis bracket voxel.  Here the same MatrixSlot type is read as a stress
-- component (output axis, input axis).  The following embedding proves literal
-- carrier reuse without claiming stress is torque.
------------------------------------------------------------------------

stressSlotAsTorqueBracket :
  SO3.SU2Axis →
  SO3.SU2Axis →
  Torque.BracketVoxel
stressSlotAsTorqueBracket output input =
  plateNormalAxis , (output , input)

stressSlotRoundTripsThroughTorqueOperatorCarrier :
  ∀ output input →
  Torque.torqueOperatorSlot (stressSlotAsTorqueBracket output input)
  ≡ (output , input)
stressSlotRoundTripsThroughTorqueOperatorCarrier output input = refl

------------------------------------------------------------------------
-- 4. Proof-relevant physical weld.
--
-- Brown-Maclay source-backs finite electromagnetic vacuum stress on the ideal
-- conducting parallel-plate system.  The source citation does not itself
-- identify a DASHI-valued stress sheet or prove agreement with the existing
-- Casimir scalar kernel.  Those are explicit same-object payments here.
------------------------------------------------------------------------

record CasimirSpatialStressSO3Weld : Set₁ where
  field
    Value : Set
    spatialStress : SpatialStressSheet Value

    brownMaclayAuthority : BrownMaclay.BrownMaclayParallelPlateAuthority

    SameIdealPlateSystem : Set
    sameIdealPlateSystem : SameIdealPlateSystem

    KernelPressureValue : Set
    kernelPressureValue : KernelPressureValue

    SamePressureObservable : Set
    normalNormalStressAgreesWithKernelPressure : SamePressureObservable

    PlateSymmetryAndStressSemantics : Set
    plateSymmetryAndStressSemantics : PlateSymmetryAndStressSemantics

    reading : String

open CasimirSpatialStressSO3Weld public

------------------------------------------------------------------------
-- 5. Mode-family C3 chart and spatial SO(3) frame are deliberately distinct.
--
-- Casimir369.modeClassAxis is an exact finite rechart of the three physical
-- mode families.  This module does not reinterpret that chart as the spatial
-- tangent/tangent/normal frame above.  Any such identification requires an
-- additional physical representation theorem.
------------------------------------------------------------------------

data ModeFamilyAxisIsPhysicalSpatialAxisByDefinition : Set where

modeFamilyAxisDoesNotBecomeSpatialAxisByDefinition :
  ModeFamilyAxisIsPhysicalSpatialAxisByDefinition → ⊥
modeFamilyAxisDoesNotBecomeSpatialAxisByDefinition ()

------------------------------------------------------------------------
-- 6. Cardinality and semantics firewalls.
------------------------------------------------------------------------

data OperatorSheetCardinalityAutomaticallyCausesCasimirDerivative : Set where
data StressOperatorSheetAutomaticallyIsTorque : Set where
data BrownMaclayCitationAutomaticallyBuildsDASHIStressSheet : Set where

data NineToThreeTractionAutomaticallyProves720To240 : Set where

operatorSheetCardinalityDoesNotCauseDerivative :
  OperatorSheetCardinalityAutomaticallyCausesCasimirDerivative → ⊥
operatorSheetCardinalityDoesNotCauseDerivative ()

stressOperatorCarrierDoesNotMakeStressTorque :
  StressOperatorSheetAutomaticallyIsTorque → ⊥
stressOperatorCarrierDoesNotMakeStressTorque ()

brownMaclayCitationNeedsSameObjectWeld :
  BrownMaclayCitationAutomaticallyBuildsDASHIStressSheet → ⊥
brownMaclayCitationNeedsSameObjectWeld ()

tractionContractionDoesNotProveCoefficientDerivative :
  NineToThreeTractionAutomaticallyProves720To240 → ⊥
tractionContractionDoesNotProveCoefficientDerivative ()

------------------------------------------------------------------------
-- 7. Machine-readable terminal status.
------------------------------------------------------------------------

record CasimirSO3StressMaxCutBoundary : Set where
  constructor casimir-so3-stress-maxcut-boundary
  field
    chosenPlateSpatialFrameOwned : Bool
    spatialStressUsesExistingNineSheet : Bool
    normalTractionNineToThreeOwned : Bool
    normalPressureThreeToOneOwned : Bool
    torqueOperatorCarrierReuseOwned : Bool
    brownMaclaySourceAuthorityAvailable : Bool

    modeFamilyChartIdentifiedWithSpatialAxes : Bool
    stressIdentifiedWithTorqueByCarrierReuse : Bool
    operatorCardinalityIdentifiedAsDerivativeCause : Bool
    sourceCitationIdentifiedAsSameObjectStressWeld : Bool

open CasimirSO3StressMaxCutBoundary public

canonicalCasimirSO3StressMaxCutBoundary : CasimirSO3StressMaxCutBoundary
canonicalCasimirSO3StressMaxCutBoundary =
  casimir-so3-stress-maxcut-boundary
    true true true true true true
    false false false false

------------------------------------------------------------------------
-- 8. Cross-pollination summary.
------------------------------------------------------------------------

casimirSO3StressReading : String
casimirSO3StressReading =
  "The parallel-plate spatial stress tensor uses the existing SO(3) 3x3 operator-sheet carrier. Contracting with the chosen plate normal gives a literal 9->3 traction map and a second contraction gives the normal-pressure component. This is the physically typed SO(3) contraction route. The earlier TEM/TE/TM three-family chart remains a separate finite representation coordinate, and the arithmetic 720->240 derivative factor is not caused by operator-sheet cardinality."
