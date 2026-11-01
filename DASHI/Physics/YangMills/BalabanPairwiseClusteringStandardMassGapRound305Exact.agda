{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact where

------------------------------------------------------------------------
-- ROUND305 / SHORTEST STANDARD-THEOREM MASS-GAP ROUTE
--
-- `BalabanPhysicalMassGapRoutes` identifies exponential clustering -> spectral
-- gap as standardImported, but its historical input record contains an unused
-- `vacuum : Observable` field.  Do not manufacture an observable merely to fill
-- stale packaging.  Normalize to the fields actually consumed by the transfer.
--
-- R304 supplies genuine arbitrary-pair continuum clustering.  The remaining
-- physical representation seam is the meaning of the concrete q=1/2 bound as
-- exponential decay at one positive physical mass/rate on the SAME reconstructed
-- Hamiltonian.  The standard spectral transfer remains an explicit authority
-- until a local theorem inhabitant is imported/certified.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap

record PairwiseClusteringMassRatePresentation
    {Measure TestObservable PhysicalObservable Hamiltonian Mass : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (pairwise : R304.PhysicalPairwiseTimePresentation dataSet extension finite)
    : Set₁ where
  field
    reconstructedHamiltonian : Hamiltonian

    massParameter : Mass
    PositiveMass : Mass → Set
    massParameterPositive : PositiveMass massParameter

    ExponentialDecayBound :
      PhysicalObservable → PhysicalObservable → Nat → ℚ → Mass → Set

    -- Same-rate semantic weld: the concrete q=1/2 inequality established by
    -- R304 is exactly the exponential-decay proposition at `massParameter`.
    quarterHalfBoundHasPhysicalMassMeaning : ∀ left right time →
      R304.continuumPairCorrelation pairwise left right time
        ≤ Shell.quarter * Power.rationalPower Geo.half time →
      ExponentialDecayBound left right time
        (R304.continuumPairCorrelation pairwise left right time)
        massParameter

open PairwiseClusteringMassRatePresentation public

record NormalizedExponentialClusteringData
    (Observable Time Scalar Mass Hamiltonian : Set) : Set₁ where
  field
    connectedCorrelation : Observable → Observable → Time → Scalar
    massParameter : Mass
    Positive : Mass → Set
    positiveMassParameter : Positive massParameter
    ExponentialDecayBound : Observable → Observable → Time → Scalar → Mass → Set
    exponentialTimeClustering : ∀ A B t →
      ExponentialDecayBound A B t (connectedCorrelation A B t) massParameter
    reconstructedHamiltonian : Hamiltonian

open NormalizedExponentialClusteringData public

asNormalizedExponentialClusteringData :
  ∀ {Measure TestObservable PhysicalObservable Hamiltonian Mass}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {pairwise : R304.PhysicalPairwiseTimePresentation dataSet extension finite} →
  PairwiseClusteringMassRatePresentation pairwise →
  NormalizedExponentialClusteringData
    PhysicalObservable Nat ℚ Mass Hamiltonian
asNormalizedExponentialClusteringData {pairwise = pairwise} presentation = record
  { NormalizedExponentialClusteringData.connectedCorrelation =
      R304.continuumPairCorrelation pairwise
  ; NormalizedExponentialClusteringData.massParameter = massParameter presentation
  ; NormalizedExponentialClusteringData.Positive = PositiveMass presentation
  ; NormalizedExponentialClusteringData.positiveMassParameter =
      massParameterPositive presentation
  ; NormalizedExponentialClusteringData.ExponentialDecayBound =
      ExponentialDecayBound presentation
  ; NormalizedExponentialClusteringData.exponentialTimeClustering =
      λ left right time →
        quarterHalfBoundHasPhysicalMassMeaning presentation left right time
          (R304.continuumPairGeometricUpper pairwise left right time)
  ; NormalizedExponentialClusteringData.reconstructedHamiltonian =
      reconstructedHamiltonian presentation
  }

record NormalizedExponentialClusteringSpectrumAuthority
    {Observable Time Scalar Mass Hamiltonian : Set}
    (dataSet : NormalizedExponentialClusteringData
      Observable Time Scalar Mass Hamiltonian) : Set₁ where
  field
    SpectrumSeparatedBy : Hamiltonian → Mass → Set
    exponentialClusteringTransfer :
      (∀ A B t →
        ExponentialDecayBound dataSet A B t
          (connectedCorrelation dataSet A B t)
          (massParameter dataSet)) →
      SpectrumSeparatedBy
        (reconstructedHamiltonian dataSet)
        (massParameter dataSet)

open NormalizedExponentialClusteringSpectrumAuthority public

compileNormalizedClusteringToMassGap :
  ∀ {Observable Time Scalar Mass Hamiltonian}
    (dataSet : NormalizedExponentialClusteringData
      Observable Time Scalar Mass Hamiltonian) →
  NormalizedExponentialClusteringSpectrumAuthority dataSet →
  OSGap.PhysicalMassGapCertificate Hamiltonian Mass
compileNormalizedClusteringToMassGap dataSet authority = record
  { OSGap.PhysicalMassGapCertificate.hamiltonian = reconstructedHamiltonian dataSet
  ; OSGap.PhysicalMassGapCertificate.gap = massParameter dataSet
  ; OSGap.PhysicalMassGapCertificate.Positive = Positive dataSet
  ; OSGap.PhysicalMassGapCertificate.gapPositive = positiveMassParameter dataSet
  ; OSGap.PhysicalMassGapCertificate.SpectrumAboveVacuumGap =
      SpectrumSeparatedBy authority
        (reconstructedHamiltonian dataSet) (massParameter dataSet)
  ; OSGap.PhysicalMassGapCertificate.spectrumAboveVacuumGap =
      exponentialClusteringTransfer authority (exponentialTimeClustering dataSet)
  }

compilePairwiseClusteringToMassGap :
  ∀ {Measure TestObservable PhysicalObservable Hamiltonian Mass}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {pairwise : R304.PhysicalPairwiseTimePresentation dataSet extension finite}
    (presentation : PairwiseClusteringMassRatePresentation pairwise) →
  NormalizedExponentialClusteringSpectrumAuthority
    (asNormalizedExponentialClusteringData presentation) →
  OSGap.PhysicalMassGapCertificate Hamiltonian Mass
compilePairwiseClusteringToMassGap presentation =
  compileNormalizedClusteringToMassGap
    (asNormalizedExponentialClusteringData presentation)

record Round305Boundary : Set where
  constructor round305-boundary
  field
    detailedSubgapSpectralContradictionMandatory : Bool
    detailedSubgapSpectralContradictionMandatoryIsFalse :
      detailedSubgapSpectralContradictionMandatory ≡ false

    arbitraryPairContinuumClusteringRequired : Bool
    arbitraryPairContinuumClusteringRequiredIsTrue :
      arbitraryPairContinuumClusteringRequired ≡ true

    physicalMassRateNormalizationRequired : Bool
    physicalMassRateNormalizationRequiredIsTrue :
      physicalMassRateNormalizationRequired ≡ true

    standardClusteringToSpectrumAuthorityRequired : Bool
    standardClusteringToSpectrumAuthorityRequiredIsTrue :
      standardClusteringToSpectrumAuthorityRequired ≡ true

    staleUnusedVacuumFieldCanBlockNormalizedRoute : Bool
    staleUnusedVacuumFieldCanBlockNormalizedRouteIsFalse :
      staleUnusedVacuumFieldCanBlockNormalizedRoute ≡ false

canonicalRound305Boundary : Round305Boundary
canonicalRound305Boundary =
  round305-boundary false refl true refl true refl true refl false refl

round305NormalizedMassGapAssemblyLevel : ProofLevel
round305NormalizedMassGapAssemblyLevel = machineChecked

round305PairwiseContinuumClusteringLevel : ProofLevel
round305PairwiseContinuumClusteringLevel = R304.round304PairwiseContinuumClusteringCompilerLevel

round305StandardClusteringToSpectrumTransferLevel : ProofLevel
round305StandardClusteringToSpectrumTransferLevel = standardImported

round305PhysicalMassRateNormalizationLevel : ProofLevel
round305PhysicalMassRateNormalizationLevel = conditional
