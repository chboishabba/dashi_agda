module DASHI.Physics.YangMills.BalabanFederbushPairedContourCancellationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Paul Federbush,
-- "A Mass Zero Cluster Expansion",
-- Communications in Mathematical Physics 81 (1981), 327--340.
-- DOI: 10.1007/BF01208900.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- PURPOSE
-- Isolate the exact hypotheses under which contour reversal cancels the linear
-- logarithmic forcing.  Order reversal, link inversion, equal weights and one
-- common logarithm branch are independent obligations.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.PhysicalInvolutionParityExact as Parity
open import DASHI.Physics.YangMills.CompactLieProofLevel

record ScalarActionParity
    (Scalar Vector : Set)
    (vector : Parity.ParityCodomain Vector) : Set₁ where
  field
    ScalarEquivalent : Scalar → Scalar → Set
    scalarEquivalentRefl : ∀ scalar → ScalarEquivalent scalar scalar

    scale : Scalar → Vector → Vector

    scaleScalarCongruent : ∀ {left right} value →
      ScalarEquivalent left right →
      Parity.Equivalent vector
        (scale left value)
        (scale right value)

    scaleVectorCongruent : ∀ scalar {left right} →
      Parity.Equivalent vector left right →
      Parity.Equivalent vector
        (scale scalar left)
        (scale scalar right)

    scaleNegate : ∀ scalar value →
      Parity.Equivalent vector
        (scale scalar (Parity.negate vector value))
        (Parity.negate vector (scale scalar value))

open ScalarActionParity public

record PairedContourLogData
    (Contour Scalar Vector : Set) : Set₁ where
  field
    contourInvolution : Parity.Involution Contour
    vector : Parity.ParityCodomain Vector
    action : ScalarActionParity Scalar Vector vector

    weight : Contour → Scalar
    contourLog : Contour → Vector

    pairedWeightsEqual : ∀ contour →
      ScalarEquivalent action
        (weight (Parity.reverse contourInvolution contour))
        (weight contour)

    contourLogOdd :
      Parity.OddUnder contourInvolution vector contourLog

    inverseContourUsesReverseOrder : Set
    inverseContourUsesReverseOrderEvidence :
      inverseContourUsesReverseOrder

    commonPrincipalLogBranch : Set
    commonPrincipalLogBranchEvidence : commonPrincipalLogBranch

open PairedContourLogData public

weightedContourLog :
  ∀ {Contour Scalar Vector} →
  PairedContourLogData Contour Scalar Vector →
  Contour → Vector
weightedContourLog dataSet contour =
  scale (action dataSet)
    (weight dataSet contour)
    (contourLog dataSet contour)

weightedContourLogOdd :
  ∀ {Contour Scalar Vector}
    (dataSet : PairedContourLogData Contour Scalar Vector) →
  ∀ contour →
  Parity.Equivalent (vector dataSet)
    (weightedContourLog dataSet
      (Parity.reverse (contourInvolution dataSet) contour))
    (Parity.negate (vector dataSet)
      (weightedContourLog dataSet contour))
weightedContourLogOdd dataSet contour =
  Parity.equivalentTrans (vector dataSet)
    (scaleScalarCongruent (action dataSet)
      (contourLog dataSet
        (Parity.reverse (contourInvolution dataSet) contour))
      (pairedWeightsEqual dataSet contour))
    (Parity.equivalentTrans (vector dataSet)
      (scaleVectorCongruent (action dataSet)
        (weight dataSet contour)
        (Parity.oddLaw (contourLogOdd dataSet) contour))
      (scaleNegate (action dataSet)
        (weight dataSet contour)
        (contourLog dataSet contour)))

pairedWeightedContourLogsCancel :
  ∀ {Contour Scalar Vector}
    (dataSet : PairedContourLogData Contour Scalar Vector) →
  ∀ contour →
  Parity.Equivalent (vector dataSet)
    (Parity.add (vector dataSet)
      (weightedContourLog dataSet contour)
      (weightedContourLog dataSet
        (Parity.reverse (contourInvolution dataSet) contour)))
    (Parity.zero (vector dataSet))
pairedWeightedContourLogsCancel dataSet contour =
  Parity.equivalentTrans (vector dataSet)
    (Parity.addCongruent (vector dataSet)
      (Parity.equivalentRefl (vector dataSet)
        (weightedContourLog dataSet contour))
      (weightedContourLogOdd dataSet contour))
    (Parity.addInverseRight (vector dataSet)
      (weightedContourLog dataSet contour))

record QuadraticCentreForcingKernel (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

open QuadraticCentreForcingKernel public

record FederbushQuadraticCentreForcing
    (Scalar : Set)
    (kernel : QuadraticCentreForcingKernel Scalar) : Set₁ where
  field
    delta centreForcing quadraticConstant : Scalar

    pairedLinearForcingCancels : Set
    pairedLinearForcingCancelsEvidence : pairedLinearForcingCancels

    nonlinearForcingBelowQuadratic :
      LessEqual kernel centreForcing
        (multiply kernel quadraticConstant
          (multiply kernel delta delta))

open FederbushQuadraticCentreForcing public

federbushCentreForcingQuadratic :
  ∀ {Scalar}
    {kernel : QuadraticCentreForcingKernel Scalar} →
  (certificate : FederbushQuadraticCentreForcing Scalar kernel) →
  LessEqual kernel
    (centreForcing certificate)
    (multiply kernel
      (quadraticConstant certificate)
      (multiply kernel (delta certificate) (delta certificate)))
federbushCentreForcingQuadratic = nonlinearForcingBelowQuadratic

pairedContourWeightCancellationLevel : ProofLevel
pairedContourWeightCancellationLevel = machineChecked

contourReverseOrderAndLogChartLevel : ProofLevel
contourReverseOrderAndLogChartLevel = conditional

federbushQuadraticCentreForcingReducerLevel : ProofLevel
federbushQuadraticCentreForcingReducerLevel = machineChecked

physicalFederbushQuadraticRemainderLevel : ProofLevel
physicalFederbushQuadraticRemainderLevel = conditional
