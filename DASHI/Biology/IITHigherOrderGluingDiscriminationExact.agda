module DASHI.Biology.IITHigherOrderGluingDiscriminationExact where

------------------------------------------------------------------------
-- HIGHER-ORDER GLUING DISCRIMINATION
--
-- The max-cut conjecture now has three logically distinct layers:
--
--   1. minimal local synthesis (Boolean parity / affine F3 channels),
--   2. ordered orientation / phase carried by gluing,
--   3. irreducible triadic face data that does not descend to pairwise/local
--      observations.
--
-- Existing non-descent already supplies a same-boundary/different-face witness.
-- This owner packages that exact witness beside the parity/torque algebra while
-- refusing to identify any one layer with IIT big-Phi or physical torque.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITBooleanParityMinimalSufficiencyExact as BooleanParity
import DASHI.Biology.IITTernaryAffineMinimalSufficiencyExact as TernaryAffine
import DASHI.Biology.IITBinaryTernaryParityTorqueLiftExact as ParityTorque
import DASHI.Biology.IITPointedTernary27TriadicNonDescentExact as Triadic
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Trialectic

------------------------------------------------------------------------
-- 1. Re-export the exact higher-order obstruction in the conjecture vocabulary.
------------------------------------------------------------------------

pairwiseSelectedCubiesDoNotRecoverTriadicFace :
  Descent.FactorsThrough
    Triadic.selectedCubiesObserver
    Triadic.triadicFaceConsumer → ⊥
pairwiseSelectedCubiesDoNotRecoverTriadicFace =
  Triadic.selectedCubiesDoNotDetermineTriadicFace

samePairwiseBoundaryWitness :
  Triadic.selectedCubiesObserver Trialectic.structuredReciprocal
  ≡ Triadic.selectedCubiesObserver Trialectic.structuredUnderdetermined
samePairwiseBoundaryWitness = Triadic.sameSelectedCubies

differentHigherFaceWitness :
  Triadic.triadicFaceConsumer Trialectic.structuredReciprocal
  ≡ Triadic.triadicFaceConsumer Trialectic.structuredUnderdetermined
  → ⊥
differentHigherFaceWitness = Triadic.differentTriadicFace

------------------------------------------------------------------------
-- 2. The local algebraic carriers are exact but have different roles.
------------------------------------------------------------------------

booleanMinimalParityWitness :
  BooleanParity.ParityOrComplement BooleanParity.xorGate
booleanMinimalParityWitness = BooleanParity.xorParity

ternarySymmetricParityWitness :
  TernaryAffine.SymmetricAffine TernaryAffine.triSumGate
ternarySymmetricParityWitness = TernaryAffine.triSumIsSymmetric

ternaryAntisymmetricOrientationWitness :
  TernaryAffine.AntisymmetricAffine TernaryAffine.triDifferenceGate
ternaryAntisymmetricOrientationWitness = TernaryAffine.triDifferenceIsAntisymmetric

ternaryDifferenceReversesSign :
  (a b : Base369.TriTruth) →
  ParityTorque.triDiff b a
  ≡ ParityTorque.triNeg (ParityTorque.triDiff a b)
ternaryDifferenceReversesSign = ParityTorque.triDiffSwapNegates

------------------------------------------------------------------------
-- 3. Authority / conjecture boundary.
------------------------------------------------------------------------

record HigherOrderGluingDiscriminationBoundary : Set where
  constructor higher-order-gluing-discrimination-boundary
  field
    parityIsLocalSynthesisLayer : Bool
    antisymmetricF3DifferenceCarriesSwapOrientation : Bool
    pairwiseBoundaryDeterminesTriadicFace : Bool
    higherFaceNonDescentIsExact : Bool
    localParityIsDefinitionallyPhysicalTorque : Bool
    torqueOrientationIsDefinitionallyIITPhi : Bool
    scalarSystemPhiAutomaticallyRecoversHigherFace : Bool
    fullIITStructureStillRequiresIndependentEvaluation : Bool

canonicalHigherOrderGluingDiscriminationBoundary :
  HigherOrderGluingDiscriminationBoundary
canonicalHigherOrderGluingDiscriminationBoundary =
  higher-order-gluing-discrimination-boundary
    true true false true false false false true
