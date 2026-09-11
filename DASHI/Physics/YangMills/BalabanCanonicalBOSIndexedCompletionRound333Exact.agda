{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCanonicalBOSIndexedCompletionRound333Exact where

------------------------------------------------------------------------
-- ROUND333 / COMPOSE THE REPAIRED CANONICAL-B APPLICATION INTERFACES
--
-- This owner adds no new analytic theorem.  It composes the preferred repaired
-- forms of the four downstream application coordinates:
--
--   H2a  OS1-indexed Euclidean-time/support semantics        (R332)
--   H2b  Wilson-cylinder bounded-test presentation           (R315)
--   H2c  shared sequential-order closure                     (R330)
--   H3   OS-reconstruction-indexed transfer coordinate       (R331)
--
-- into the already-owned pairwise clustering -> physical mass-gap compiler
-- (R310/R304/R316).  H1 remains upstream in the finite T5 presentation.
--
-- The point is least privilege: once these proof-bearing application objects
-- exist, no historical arbitrary timeTranslate, three unrelated boundedness
-- receipts, duplicate order-closure theorem, or arbitrary Hamiltonian pairing
-- remains on the route.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSCompactGammaGalerkinLimitBridge as Sequential
import DASHI.Physics.Closure.NSTriadKNIntegratedDangerOccupationWeldRound92Exact as RationalNS
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact as R330
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanOSIndexedTransferCoordinateRound331Exact as R331
import DASHI.Physics.YangMills.BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact as R332
import DASHI.Physics.YangMills.BalabanHalfRateTransferCoordinateMassGapRound316Exact as R316

RationalSequentialOrderClosure : Set₁
RationalSequentialOrderClosure =
  Sequential.SequentialOrderClosure RationalNS.rationalAbsorptionArithmetic

record CanonicalBOSIndexedApplication
    {Measure TestObservable PhysicalObservable Loop Translation Rotation : Set}
    {Observable Point Scalar : Set}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (finite : R296.ExactT5JMagnitudePresentation dataSet extension)
    (assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ)
    (reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system)
    (Energy : Set) : Set₁ where
  field
    euclideanSemantics :
      R332.OSIndexedPairwiseEuclideanSemantics
        {PhysicalObservable = PhysicalObservable}
        {dataSet = dataSet} {extension = extension} {finite = finite}
        assembly

    wilsonPresentation :
      R315.PairwiseWilsonCylinderPresentation {Loop = Loop}
        (R332.asR310PairwiseEuclideanTimeSemantics assembly euclideanSemantics)

    sequentialClosure : RationalSequentialOrderClosure
    convergenceWeld :
      R330.T5SequentialOrderClosureWeld dataSet sequentialClosure

    transferCoordinate :
      R331.OSIndexedTransferCoordinate reconstruction Energy

open CanonicalBOSIndexedApplication public

historicalSemantics :
  ∀ {Measure TestObservable PhysicalObservable Loop Translation Rotation}
    {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set} →
  CanonicalBOSIndexedApplication
    {PhysicalObservable = PhysicalObservable} {Loop = Loop}
    dataSet extension finite assembly reconstruction Energy →
  R310.PairwiseEuclideanTimeSemantics
    {PhysicalObservable = PhysicalObservable}
    {dataSet = dataSet} {extension = extension} {finite = finite}
historicalSemantics {assembly = assembly} application =
  R332.asR310PairwiseEuclideanTimeSemantics
    assembly (euclideanSemantics application)

boundedTests :
  ∀ {Measure TestObservable PhysicalObservable Loop Translation Rotation}
    {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set}
    (application : CanonicalBOSIndexedApplication
      {PhysicalObservable = PhysicalObservable} {Loop = Loop}
      dataSet extension finite assembly reconstruction Energy) →
  R310.PairwiseBoundedTestAdmissibility (historicalSemantics application)
boundedTests application =
  R315.asPairwiseBoundedTestAdmissibility
    (historicalSemantics application)
    (wilsonPresentation application)

orderClosure :
  ∀ {Measure TestObservable PhysicalObservable Loop Translation Rotation}
    {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set}
    (application : CanonicalBOSIndexedApplication
      {PhysicalObservable = PhysicalObservable} {Loop = Loop}
      dataSet extension finite assembly reconstruction Energy) →
  R310.RationalUpperOrderClosure dataSet
orderClosure application =
  R330.toR310RationalUpperOrderClosure
    (sequentialClosure application) (convergenceWeld application)

pairwisePresentation :
  ∀ {Measure TestObservable PhysicalObservable Loop Translation Rotation}
    {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set}
    (application : CanonicalBOSIndexedApplication
      {PhysicalObservable = PhysicalObservable} {Loop = Loop}
      dataSet extension finite assembly reconstruction Energy) →
  DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact.PhysicalPairwiseTimePresentation
    dataSet extension finite
pairwisePresentation application =
  R310.asPhysicalPairwiseTimePresentation
    (historicalSemantics application)
    (boundedTests application)
    (orderClosure application)

historicalTransfer :
  ∀ {Measure TestObservable PhysicalObservable Loop Translation Rotation}
    {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set}
    (application : CanonicalBOSIndexedApplication
      {PhysicalObservable = PhysicalObservable} {Loop = Loop}
      dataSet extension finite assembly reconstruction Energy) →
  DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact.SameHamiltonianTransferCoordinate
    (OS.Hamiltonian reconstruction) Energy
historicalTransfer {reconstruction = reconstruction} application =
  R331.asHistoricalSameHamiltonianTransferCoordinate
    reconstruction (transferCoordinate application)

record CanonicalBOSIndexedCompletion
    {Measure TestObservable PhysicalObservable Loop Translation Rotation : Set}
    {Observable Point Scalar : Set}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set}
    (application : CanonicalBOSIndexedApplication
      {PhysicalObservable = PhysicalObservable} {Loop = Loop}
      dataSet extension finite assembly reconstruction Energy) : Set₁ where
  field
    spectralAuthority :
      R316.HalfRateClusteringSpectrumAuthority
        (pairwisePresentation application)
        (historicalTransfer application)

open CanonicalBOSIndexedCompletion public

compileCanonicalBOSIndexedCompletion :
  ∀ {Measure TestObservable PhysicalObservable Loop Translation Rotation}
    {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set}
    {application : CanonicalBOSIndexedApplication
      {PhysicalObservable = PhysicalObservable} {Loop = Loop}
      dataSet extension finite assembly reconstruction Energy} →
  CanonicalBOSIndexedCompletion application →
  OS.PhysicalMassGapCertificate (OS.Hamiltonian reconstruction) Energy
compileCanonicalBOSIndexedCompletion {application = application} completion =
  R316.compileHalfRateClusteringToMassGap
    (historicalTransfer application)
    (spectralAuthority completion)

round333ApplicationCompilerLevel : ProofLevel
round333ApplicationCompilerLevel = machineChecked

-- No theorem status is promoted: the proof-bearing application fields retain
-- the levels owned by R315/R330/R331/R332 and the imported R316 spectral theorem.
