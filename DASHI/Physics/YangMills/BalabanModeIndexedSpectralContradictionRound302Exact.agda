{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanModeIndexedSpectralContradictionRound302Exact where

------------------------------------------------------------------------
-- ROUND302 / DIRECT MODE-INDEXED SPECTRAL CONTRADICTION
--
-- The old R288/R301 envelope interface asks for an envelope at arbitrary
-- (energy, observable), although canonical cyclicity supplies an observable FROM
-- a particular nonzero subgap mode.  Constructing an inverse observable -> mode
-- is unnecessary and in general unavailable.
--
-- The terminal consumer only quantifies a hypothetical subgap mode.  Work on
-- that exact fibre:
--
--   mode -> cyclic observable -> positive spectral component <= correlation
--        -> direct B1 correlation upper <= (1/4)(1/2)^t
--
-- and use the local energy->ratio order only for that same mode.  No inverse
-- observable map and no global Q->Energy map occur.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as GeoSep
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record ModeIndexedSpectralRateData
    {Measure TestObservable Energy Vector : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector)
    (family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative))
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family) : Set₁ where
  field
    zeroEnergy gapCandidate : Energy
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set

    ratioOfEnergy : Energy → ℚ

    candidateRatioIsHalf : ratioOfEnergy gapCandidate ≡ Geo.half

    ratioNonnegativeForPositiveEnergy : ∀ energy →
      PositiveEnergy energy → 0ℚ ≤ ratioOfEnergy energy

    positiveEnergyFromStrictDecay : ∀ energy →
      0ℚ ≤ ratioOfEnergy energy → ratioOfEnergy energy < 1ℚ →
      PositiveEnergy energy

    positiveEnergyHasStrictDecay : ∀ energy →
      PositiveEnergy energy → ratioOfEnergy energy < 1ℚ

    positiveSubgapHasSlowerDecay : ∀ energy →
      PositiveEnergy energy → StrictlyBelow energy gapCandidate →
      Geo.half < ratioOfEnergy energy

    -- SAME spectral rate: the positive component selected by R300 uses the
    -- physical ratio of this exact energy, not an independently named q.
    componentRatioIsEnergyRatio : ∀ energy mode →
      R300.subgapRatio decomposition energy mode ≡ ratioOfEnergy energy

    -- Direct canonical B1 upper on exactly the covariance selected by the mode.
    -- R284/R296 are producer routes for this field; R302 does not require their
    -- larger records once the terminal inequality is available.
    modeCorrelationBelowFastEnvelope : ∀ energy mode time →
      let observable =
            R297.modeObservableFromActualNonzeroFamily family energy mode
      in
      R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests (R300.indexFor decomposition observable time))
        (R278.right tests (R300.indexFor decomposition observable time))
      ≤ Shell.quarter * Power.rationalPower Geo.half time

open ModeIndexedSpectralRateData public

candidateRatioNonnegative :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    (rates : ModeIndexedSpectralRateData
      dataSet extension tests quantitative family decomposition) →
  0ℚ ≤ ratioOfEnergy rates (gapCandidate rates)
candidateRatioNonnegative rates =
  subst (λ q → 0ℚ ≤ q) (sym (candidateRatioIsHalf rates)) Geo.halfNonnegative

candidateRatioStrictlyBelowOne :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    (rates : ModeIndexedSpectralRateData
      dataSet extension tests quantitative family decomposition) →
  ratioOfEnergy rates (gapCandidate rates) < 1ℚ
candidateRatioStrictlyBelowOne rates =
  subst (λ q → q < 1ℚ) (sym (candidateRatioIsHalf rates)) R274.halfStrictlyBelowOne

candidateEnergyPositive :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    (rates : ModeIndexedSpectralRateData
      dataSet extension tests quantitative family decomposition) →
  PositiveEnergy rates (gapCandidate rates)
candidateEnergyPositive rates =
  positiveEnergyFromStrictDecay rates (gapCandidate rates)
    (candidateRatioNonnegative rates)
    (candidateRatioStrictlyBelowOne rates)

NoPositiveSubgapMode :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  ModeIndexedSpectralRateData
    dataSet extension tests quantitative family decomposition → Set
NoPositiveSubgapMode {family = family} rates =
  ∀ energy → PositiveEnergy rates energy →
    StrictlyBelow rates energy (gapCandidate rates) →
    R297.SubgapMode family energy → Gap.Empty

excludePositiveSubgapModes :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    (dominance : GeoSep.RationalGeometricDominance)
    (rates : ModeIndexedSpectralRateData
      dataSet extension tests quantitative family decomposition) →
  NoPositiveSubgapMode rates
excludePositiveSubgapModes
    {extension = extension} {family = family} {decomposition = decomposition}
    dominance rates energy positive below mode =
  let
    observable = R297.modeObservableFromActualNonzeroFamily family energy mode
    weight = R300.selectedOverlapWeight decomposition energy mode
    componentRatio = R300.subgapRatio decomposition energy mode

    weightPositive = R300.selectedOverlapWeightPositive decomposition energy mode

    slowerEnergy = positiveSubgapHasSlowerDecay rates energy positive below
    slowerComponent : Geo.half < componentRatio
    slowerComponent =
      subst (λ q → Geo.half < q)
        (sym (componentRatioIsEnergyRatio rates energy mode)) slowerEnergy

    componentStrict : componentRatio < 1ℚ
    componentStrict =
      subst (λ q → q < 1ℚ)
        (sym (componentRatioIsEnergyRatio rates energy mode))
        (positiveEnergyHasStrictDecay rates energy positive)

    witness = GeoSep.eventuallySlowDominatesFast dominance
      Shell.quarter weight componentRatio
      R274.quarterNonnegative weightPositive slowerComponent componentStrict
    time = Agda.Builtin.Sigma.fst witness
    fastBelowSlow = Agda.Builtin.Sigma.snd witness

    lower = R300.spectralComponentBelowCorrelation
      decomposition energy mode time
    upper = modeCorrelationBelowFastEnvelope rates energy mode time
  in
  GeoSep.strictSandwichImpossible lower upper fastBelowSlow

record Round302Boundary : Set where
  constructor round302-boundary
  field
    observableToModeInverseRequired : Bool
    observableToModeInverseRequiredIsFalse : observableToModeInverseRequired ≡ false

    globalRatioToEnergyInverseRequired : Bool
    globalRatioToEnergyInverseRequiredIsFalse :
      globalRatioToEnergyInverseRequired ≡ false

    separateSpectralLowerLeafRequired : Bool
    separateSpectralLowerLeafRequiredIsFalse :
      separateSpectralLowerLeafRequired ≡ false

    directModeIndexedContradictionCompilerOwned : Bool
    directModeIndexedContradictionCompilerOwnedIsTrue :
      directModeIndexedContradictionCompilerOwned ≡ true

canonicalRound302Boundary : Round302Boundary
canonicalRound302Boundary =
  round302-boundary false refl false refl false refl true refl

round302ModeIndexedContradictionCompilerLevel : ProofLevel
round302ModeIndexedContradictionCompilerLevel = machineChecked

-- Genuine spectral source seam after the compiler reduction: one same-Hamiltonian
-- positive-component decomposition plus local energy/ratio semantics on the exact
-- reconstructed continuum covariance carrier.  Positive-time cyclicity remains
-- an upstream physical realization of the quantitative cyclicity record.
round302SameHamiltonianSpectralRateRealizationLevel : ProofLevel
round302SameHamiltonianSpectralRateRealizationLevel = conditional
