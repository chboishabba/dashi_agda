{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHalfRateTransferCoordinateMassGapRound316Exact where

------------------------------------------------------------------------
-- ROUND316 / REMOVE ABSTRACT H3b OVERPAYMENT
--
-- R311 already reuses one physical transfer-energy <-> decay-ratio coordinate
-- on the SAME reconstructed Hamiltonian.  R305 then wraps the standard
-- clustering->spectrum theorem behind an arbitrary `ExponentialDecayBound`
-- predicate and asks for a second semantic implication saying that the concrete
-- q = 1/2 inequality has that meaning.
--
-- That extra predicate is not physical YM information.  The standard theorem
-- can be normalized directly to the concrete ratio statement it consumes:
--
--   C_{A,B}(t) <= (1/4) (1/2)^t
--       -> spectrum is separated by energyOfRatio(1/2).
--
-- The standard spectral theorem remains an explicit imported authority.  The
-- physical same-Hamiltonian transfer coordinate remains an explicit conditional
-- payment.  This owner removes only the representation-only H3b wrapper.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as R302
import DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact as R311
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap

record HalfRateClusteringSpectrumAuthority
    {Measure TestObservable PhysicalObservable Hamiltonian Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (pairwise : R304.PhysicalPairwiseTimePresentation dataSet extension finite)
    (transfer : R311.SameHamiltonianTransferCoordinate Hamiltonian Energy)
    : Set₁ where
  field
    SpectrumSeparatedBy : Hamiltonian → Energy → Set

    halfRateClusteringTransfer :
      (∀ left right time →
        R304.continuumPairCorrelation pairwise left right time
        ≤ Geo.quarter * Power.rationalPower Geo.half time) →
      SpectrumSeparatedBy
        (R311.reconstructedHamiltonian transfer)
        (R302.candidateEnergy (R311.coordinate transfer))

open HalfRateClusteringSpectrumAuthority public

compileHalfRateClusteringToMassGap :
  ∀ {Measure TestObservable PhysicalObservable Hamiltonian Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {pairwise : R304.PhysicalPairwiseTimePresentation dataSet extension finite}
    (transfer : R311.SameHamiltonianTransferCoordinate Hamiltonian Energy) →
  HalfRateClusteringSpectrumAuthority pairwise transfer →
  OSGap.PhysicalMassGapCertificate Hamiltonian Energy
compileHalfRateClusteringToMassGap {pairwise = pairwise} transfer authority = record
  { OSGap.PhysicalMassGapCertificate.hamiltonian =
      R311.reconstructedHamiltonian transfer
  ; OSGap.PhysicalMassGapCertificate.gap =
      R302.candidateEnergy (R311.coordinate transfer)
  ; OSGap.PhysicalMassGapCertificate.Positive =
      R302.PositiveEnergy (R311.coordinate transfer)
  ; OSGap.PhysicalMassGapCertificate.gapPositive =
      R302.candidateEnergyPositive (R311.coordinate transfer)
  ; OSGap.PhysicalMassGapCertificate.SpectrumAboveVacuumGap =
      SpectrumSeparatedBy authority
        (R311.reconstructedHamiltonian transfer)
        (R302.candidateEnergy (R311.coordinate transfer))
  ; OSGap.PhysicalMassGapCertificate.spectrumAboveVacuumGap =
      halfRateClusteringTransfer authority
        (R304.continuumPairGeometricUpper pairwise)
  }

record Round316Boundary : Set where
  constructor round316-boundary
  field
    abstractExponentialDecayPredicateRequired : Bool
    abstractExponentialDecayPredicateRequiredIsFalse :
      abstractExponentialDecayPredicateRequired ≡ false

    separateHalfRateMeaningPhysicalLeafRequired : Bool
    separateHalfRateMeaningPhysicalLeafRequiredIsFalse :
      separateHalfRateMeaningPhysicalLeafRequired ≡ false

    sameHamiltonianTransferCoordinateStillPhysical : Bool
    sameHamiltonianTransferCoordinateStillPhysicalIsTrue :
      sameHamiltonianTransferCoordinateStillPhysical ≡ true

    concreteHalfRateSpectralTransferStillImported : Bool
    concreteHalfRateSpectralTransferStillImportedIsTrue :
      concreteHalfRateSpectralTransferStillImported ≡ true

canonicalRound316Boundary : Round316Boundary
canonicalRound316Boundary =
  round316-boundary false refl false refl true refl true refl

round316CompilerLevel : ProofLevel
round316CompilerLevel = machineChecked

round316PhysicalTransferCoordinateLevel : ProofLevel
round316PhysicalTransferCoordinateLevel =
  R302.round302PhysicalTransferEnergyDecayCoordinateLevel

-- Standard OS/semigroup spectral theorem, normalized to the concrete q=1/2
-- premise rather than hidden behind an arbitrary predicate carrier.
round316HalfRateClusteringSpectrumTransferLevel : ProofLevel
round316HalfRateClusteringSpectrumTransferLevel = standardImported
