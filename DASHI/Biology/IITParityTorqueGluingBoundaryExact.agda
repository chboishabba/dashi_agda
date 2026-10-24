module DASHI.Biology.IITParityTorqueGluingBoundaryExact where

------------------------------------------------------------------------
-- PARITY INTEGRATION != ORDERED-BRACKET HANDEDNESS
--
-- The IIT branch owns a precise Boolean minimal-sufficiency result.  Sibling
-- PR #1164 now owns a broader mechanism-neutral oriented three-axis bracket
-- specialization used by torque, EM/right-hand-rule, SU(2)/YM and NS consumers.
-- Its finite 369/C3 chart remains distinct from the separately recovered
-- source-backed Balaban spatial C3 action until a same-object intertwiner is
-- paid.  This owner records that source state without importing sibling theorem
-- authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITBooleanParityMinimalSufficiencyExact as Parity

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

xorSwapInvariant : (a b : Bool) → xor a b ≡ xor b a
xorSwapInvariant false false = refl
xorSwapInvariant false true = refl
xorSwapInvariant true false = refl
xorSwapInvariant true true = refl

xorOnlyObserverSwapInvariant :
  {Observation : Set} →
  (observer : Bool → Observation) →
  (a b : Bool) →
  observer (xor a b) ≡ observer (xor b a)
xorOnlyObserverSwapInvariant observer a b
  rewrite xorSwapInvariant a b = refl

record TorqueSiblingSourceReceipt : Set where
  constructor torque-sibling-source-receipt
  field
    siblingPR : Nat
    observedHead : String
    sourceWritesOrderedOutputLeverForceVoxel : Bool
    sourceWritesSwapNegatesOrientation : Bool
    sourceWritesSwapConjugatesC3Phase : Bool
    sourceWritesDepthThreePantsRechart : Bool
    sourceWritesNestedT9Dialectic : Bool
    sourceWritesCompatibleT18Boundary : Bool
    sourceKeepsIrreducibleTriadicFaceSeparate : Bool
    sourceExtractsMechanismNeutralOrientedBracket : Bool
    sourceWiresEMRightHandRule : Bool
    sourceWiresSU2YMBracketOrientation : Bool
    sourceWiresNSCrossOrientation : Bool
    sourceRecoversBalabanSpatialC3 : Bool
    sourceKeepsFinite369C3DistinctFromBalabanC3WithoutIntertwiner : Bool
    siblingTheoremAuthorityImportedHere : Bool

canonicalTorqueSiblingSourceReceipt : TorqueSiblingSourceReceipt
canonicalTorqueSiblingSourceReceipt =
  torque-sibling-source-receipt
    1164
    "0ea864b33162999f2ad4ba99eb264023f3a6c8e0"
    true true true true true true true
    true true true true true true
    false

record ParityTorqueGluingBoundary : Set where
  constructor parity-torque-gluing-boundary
  field
    essentialBalancedBooleanClassIsParity : Bool
    parityOutputAloneDistinguishesInputOrder : Bool
    orderedGluingNeededForHandedness : Bool
    orientedBracketIsSameAsEveryPhysicalMechanism : Bool
    torqueMagnitudeIdentifiedWithParityBit : Bool
    localParityManufacturesIrreducibleTriadicFace : Bool
    finite369C3AutomaticallyEqualsBalabanSpatialC3 : Bool
    siblingTorqueAuthorityImported : Bool

canonicalParityTorqueGluingBoundary : ParityTorqueGluingBoundary
canonicalParityTorqueGluingBoundary =
  parity-torque-gluing-boundary
    true false true false false false false false

parityStructuralWitness : Parity.ParityOrComplement Parity.xorGate
parityStructuralWitness = Parity.xorParity
