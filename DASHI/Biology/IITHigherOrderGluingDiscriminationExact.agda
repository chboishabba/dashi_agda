module DASHI.Biology.IITHigherOrderGluingDiscriminationExact where

------------------------------------------------------------------------
-- HIGHER-ORDER GLUING DISCRIMINATION
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369
import DASHI.Biology.IITBooleanParityMinimalSufficiencyExact as BooleanParity
import DASHI.Biology.IITTernaryAffineMinimalSufficiencyExact as TernaryAffine
import DASHI.Biology.IITBinaryTernaryParityTorqueLiftExact as ParityTorque
import DASHI.Biology.IITPointedTernary27TriadicNonDescentExact as Triadic
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Trialectic

------------------------------------------------------------------------
-- 1. Exact higher-order obstruction.
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
-- 2. Local algebraic carriers have distinct roles.
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
