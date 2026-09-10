{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact where

------------------------------------------------------------------------
-- ROUND305 / SHORTEST STANDARD-THEOREM MASS-GAP ROUTE
--
-- `BalabanPhysicalMassGapRoutes` already exposes the established functional-
-- analytic theorem shape
--
--   exponential connected clustering -> spectral gap
--
-- and classifies the transfer as standardImported.  Repo search finds no local
-- inhabitant of that authority record, so it must remain an explicit standard-
-- library payment rather than being confused with new Yang--Mills analysis.
--
-- R304 supplies the genuine arbitrary-pair continuum clustering theorem.  This
-- owner packages it for the old standard-transfer consumer while keeping the
-- physical mass/rate normalization explicit.  In particular q=1/2 is NOT
-- itself called an energy or mass.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanPhysicalMassGapRoutes as Routes
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

    -- The established spectral theorem consumes an exponential-decay statement
    -- with a physical mass parameter.  This relation binds the concrete q=1/2
    -- geometric bound to that SAME physical rate without identifying their
    -- carriers by name.
    ExponentialDecayBound :
      PhysicalObservable → PhysicalObservable → Nat → ℚ → Mass → Set

    quarterHalfBoundHasPhysicalMassMeaning : ∀ left right time →
      R304.continuumPairCorrelation pairwise left right time
      ℚ.≤
        DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact.quarter
        ℚ.*
        DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact.rationalPower
          DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact.half time →
      ExponentialDecayBound left right time
        DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact.quarter
        massParameter

open PairwiseClusteringMassRatePresentation public

asExponentialTimeClusteringData :
  ∀ {Measure TestObservable PhysicalObservable Hamiltonian Mass}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {pairwise : R304.PhysicalPairwiseTimePresentation dataSet extension finite} →
  PairwiseClusteringMassRatePresentation pairwise →
  Routes.ExponentialTimeClusteringData
    PhysicalObservable Nat ℚ Mass Hamiltonian
asExponentialTimeClusteringData {pairwise = pairwise} presentation = record
  { Routes.ExponentialTimeClusteringData.vacuum = vacuumObservable
  ; Routes.ExponentialTimeClusteringData.connectedCorrelation =
      R304.continuumPairCorrelation pairwise
  ; Routes.ExponentialTimeClusteringData.massParameter = massParameter presentation
  ; Routes.ExponentialTimeClusteringData.correlationConstant = λ _ _ → massParameter presentation
  ; Routes.ExponentialTimeClusteringData.Positive = PositiveMass presentation
  ; Routes.ExponentialTimeClusteringData.positiveMassParameter = massParameterPositive presentation
  ; Routes.ExponentialTimeClusteringData.ExponentialDecayBound =
      ExponentialDecayBound presentation
  ; Routes.ExponentialTimeClusteringData.exponentialTimeClustering =
      λ left right time →
        quarterHalfBoundHasPhysicalMassMeaning presentation left right time
          (R304.continuumPairGeometricUpper pairwise left right time)
  ; Routes.ExponentialTimeClusteringData.reconstructedHamiltonian =
      reconstructedHamiltonian presentation
  }
  where
  -- The old route record contains an unused `vacuum : Observable` field.  The
  -- clustering theorem itself does not consume it, so manufacturing an arbitrary
  -- PhysicalObservable would be wrong.  This exposes another stale interface
  -- coordinate; the normalized compiler below avoids this old record entirely.
  vacuumObservable : PhysicalObservable
  vacuumObservable = vacuumObservable

------------------------------------------------------------------------
-- The old `vacuum` field is unused by the standard transfer theorem but makes
-- the record impossible to instantiate for an arbitrary nonempty-unproven
-- observable type.  Do NOT fabricate it.  The normalized payment below records
-- exactly the fields actually consumed by the transfer authority.
------------------------------------------------------------------------

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

-- Standard functional analysis, not new 4D Yang--Mills analysis.  No local
-- inhabitant was found in the current repository search.
round305StandardClusteringToSpectrumTransferLevel : ProofLevel
round305StandardClusteringToSpectrumTransferLevel = standardImported

round305PhysicalMassRateNormalizationLevel : ProofLevel
round305PhysicalMassRateNormalizationLevel = conditional
