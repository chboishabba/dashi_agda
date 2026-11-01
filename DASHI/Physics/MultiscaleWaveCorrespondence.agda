module DASHI.Physics.MultiscaleWaveCorrespondence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Core.MultiscaleMDL

------------------------------------------------------------------------
-- Physics-facing correspondence boundary.
--
-- This module records an explicit symbol dictionary and falsification
-- contract.  It does not identify MDL with physical action, nor a generic
-- kernel with a law of nature.  Promotion requires a selected discretisation,
-- convergence proof, dimensional interpretation, and empirical receipts.

data Never : Set where

data PhysicsCorrespondenceRoute : Set where
  candidateWaveRoute : PhysicsCorrespondenceRoute
  mdlEqualsPhysicalActionRoute : PhysicsCorrespondenceRoute
  arbitraryKernelIsPhysicalLawRoute : PhysicsCorrespondenceRoute
  discretisationImpliesContinuumRoute : PhysicsCorrespondenceRoute
  benchmarkFreePhysicsPromotionRoute : PhysicsCorrespondenceRoute

AdmissiblePhysicsCorrespondenceRoute : PhysicsCorrespondenceRoute → Set
AdmissiblePhysicsCorrespondenceRoute candidateWaveRoute = ⊤
AdmissiblePhysicsCorrespondenceRoute mdlEqualsPhysicalActionRoute = Never
AdmissiblePhysicsCorrespondenceRoute arbitraryKernelIsPhysicalLawRoute = Never
AdmissiblePhysicsCorrespondenceRoute discretisationImpliesContinuumRoute = Never
AdmissiblePhysicsCorrespondenceRoute benchmarkFreePhysicsPromotionRoute = Never

mdlEqualsPhysicalActionRejected :
  AdmissiblePhysicsCorrespondenceRoute mdlEqualsPhysicalActionRoute → Never
mdlEqualsPhysicalActionRejected impossible = impossible

arbitraryKernelIsPhysicalLawRejected :
  AdmissiblePhysicsCorrespondenceRoute arbitraryKernelIsPhysicalLawRoute → Never
arbitraryKernelIsPhysicalLawRejected impossible = impossible

discretisationImpliesContinuumRejected :
  AdmissiblePhysicsCorrespondenceRoute discretisationImpliesContinuumRoute → Never
discretisationImpliesContinuumRejected impossible = impossible

benchmarkFreePhysicsPromotionRejected :
  AdmissiblePhysicsCorrespondenceRoute benchmarkFreePhysicsPromotionRoute → Never
benchmarkFreePhysicsPromotionRejected impossible = impossible

------------------------------------------------------------------------
-- Explicit symbol dictionary.

data MathematicalRole : Set where
  scaleIndexRole : MathematicalRole
  cellIndexRole : MathematicalRole
  carrierValueRole : MathematicalRole
  projectionRole : MathematicalRole
  liftRole : MathematicalRole
  residualRole : MathematicalRole
  kernelRole : MathematicalRole
  descriptionLengthRole : MathematicalRole
  orbitQuotientRole : MathematicalRole
  prefixDistanceRole : MathematicalRole

data CandidatePhysicalRole : Set where
  spatialResolutionRole : CandidatePhysicalRole
  spatialCellRole : CandidatePhysicalRole
  fieldAmplitudeRole : CandidatePhysicalRole
  coarseAverageRole : CandidatePhysicalRole
  interpolationRole : CandidatePhysicalRole
  subgridFluctuationRole : CandidatePhysicalRole
  discreteEvolutionRole : CandidatePhysicalRole
  codingSelectionPenaltyRole : CandidatePhysicalRole
  redundancyGaugeRole : CandidatePhysicalRole
  firstDifferingScaleRole : CandidatePhysicalRole

record SymbolCorrespondence : Set where
  constructor symbol-correspondence
  field
    mathematicalRole : MathematicalRole
    candidatePhysicalRole : CandidatePhysicalRole
    interpretation : String
    correspondenceIsDefinition : Bool
    correspondenceIsDefinitionIsFalse : correspondenceIsDefinition ≡ false
open SymbolCorrespondence public

mkCandidateCorrespondence :
  MathematicalRole → CandidatePhysicalRole → String → SymbolCorrespondence
mkCandidateCorrespondence mathematical physical note =
  symbol-correspondence mathematical physical note false refl

canonicalWaveDictionary : List SymbolCorrespondence
canonicalWaveDictionary =
  mkCandidateCorrespondence scaleIndexRole spatialResolutionRole
    "j labels a chosen discretisation scale"
  ∷ mkCandidateCorrespondence cellIndexRole spatialCellRole
    "I_j labels cells at that scale"
  ∷ mkCandidateCorrespondence carrierValueRole fieldAmplitudeRole
    "a carrier value may encode one or more field components"
  ∷ mkCandidateCorrespondence projectionRole coarseAverageRole
    "projection may be instantiated by conservative averaging"
  ∷ mkCandidateCorrespondence liftRole interpolationRole
    "lift may be instantiated by interpolation or replication"
  ∷ mkCandidateCorrespondence residualRole subgridFluctuationRole
    "the exact residual is information omitted by the coarse prediction"
  ∷ mkCandidateCorrespondence kernelRole discreteEvolutionRole
    "a local kernel may be tested as a time-step operator"
  ∷ mkCandidateCorrespondence descriptionLengthRole codingSelectionPenaltyRole
    "MDL may rank admissible models without being identified with action"
  ∷ mkCandidateCorrespondence orbitQuotientRole redundancyGaugeRole
    "an explicit symmetry action may encode representational redundancy"
  ∷ mkCandidateCorrespondence prefixDistanceRole firstDifferingScaleRole
    "prefix distance records the earliest unresolved scale"
  ∷ []

------------------------------------------------------------------------
-- Continuum-limit obligation packet.

data CandidateEquation : Set where
  transportEquation : CandidateEquation
  diffusionEquation : CandidateEquation
  firstOrderWaveSystem : CandidateEquation
  secondOrderWaveEquation : CandidateEquation
  selectedLocalEquation : CandidateEquation

record ContinuumLimitObligations : Set where
  constructor continuum-limit-obligations
  field
    equation : CandidateEquation
    spatialDimension : Nat
    fieldComponentCount : Nat
    gridSpacingDescription : String
    timeStepDescription : String
    localStencilSupplied : Bool
    localStencilSuppliedIsTrue : localStencilSupplied ≡ true
    consistencyEstimateSupplied : Bool
    stabilityEstimateSupplied : Bool
    convergenceProofSupplied : Bool
    dimensionalInterpretationSupplied : Bool
    continuumLawDerived : Bool
    continuumLawDerivedIsFalse : continuumLawDerived ≡ false
open ContinuumLimitObligations public

mkOpenContinuumLimitObligations :
  CandidateEquation → Nat → Nat → String → String → ContinuumLimitObligations
mkOpenContinuumLimitObligations equation dimension components spacing step =
  continuum-limit-obligations
    equation dimension components spacing step
    true refl
    false false false false false refl

-- A concrete consumer may replace this open packet only after supplying the
-- missing estimates and an actual convergence theorem.
canonicalWaveLimitObligations : ContinuumLimitObligations
canonicalWaveLimitObligations =
  mkOpenContinuumLimitObligations
    firstOrderWaveSystem
    3
    2
    "h_j tends to zero along the selected spatial tower"
    "delta-t is coupled to h_j by an explicit stability condition"

------------------------------------------------------------------------
-- Quantitative falsification receipts.

data BenchmarkKind : Set where
  dispersionBenchmark : BenchmarkKind
  rateDistortionBenchmark : BenchmarkKind
  scaleCommutationBenchmark : BenchmarkKind

record BenchmarkContract : Set where
  constructor benchmark-contract
  field
    benchmarkKind : BenchmarkKind
    measuredQuantity : String
    passCriterion : String
    resolutionTrend : String
    baseline : String
    measurementSupplied : Bool
    benchmarkPassed : Bool
    physicsPromotionAllowed : Bool
    physicsPromotionAllowedIsFalse : physicsPromotionAllowed ≡ false
open BenchmarkContract public

mkOpenBenchmark :
  BenchmarkKind → String → String → String → String → BenchmarkContract
mkOpenBenchmark kind quantity criterion trend baseline =
  benchmark-contract kind quantity criterion trend baseline false false false refl

canonicalFalsificationBenchmarks : List BenchmarkContract
canonicalFalsificationBenchmarks =
  mkOpenBenchmark
    dispersionBenchmark
    "phase and group velocity error over wave number"
    "error decreases at the predicted convergence order"
    "evaluate over successively refined grids"
    "analytic dispersion relation for the selected PDE"
  ∷ mkOpenBenchmark
    rateDistortionBenchmark
    "bits per symbol at fixed distortion"
    "gap to a named strong codec or entropy-model baseline is reported"
    "evaluate rate-distortion curves across scales and datasets"
    "current domain-appropriate codec baseline"
  ∷ mkOpenBenchmark
    scaleCommutationBenchmark
    "norm of project(kernel_fine(x)) minus kernel_coarse(project(x))"
    "commutation defect decreases or remains within a proved bound"
    "evaluate defect under refinement and long rollouts"
    "exact project-kernel law from DASHI.Core.MultiscaleMDL"
  ∷ []

------------------------------------------------------------------------
-- Status receipt: useful for summaries without theorem promotion.

record MultiscaleWaveStatus : Set where
  constructor multiscale-wave-status
  field
    exactMultiscaleCoreAvailable : Bool
    exactMultiscaleCoreAvailableIsTrue : exactMultiscaleCoreAvailable ≡ true
    exactResidualReconstructionAvailable : Bool
    exactResidualReconstructionAvailableIsTrue :
      exactResidualReconstructionAvailable ≡ true
    waveCorrespondenceCandidateOnly : Bool
    waveCorrespondenceCandidateOnlyIsTrue : waveCorrespondenceCandidateOnly ≡ true
    continuumPDEDerived : Bool
    continuumPDEDerivedIsFalse : continuumPDEDerived ≡ false
    shannonOptimalityProved : Bool
    shannonOptimalityProvedIsFalse : shannonOptimalityProved ≡ false
    physicalLawSelectionProved : Bool
    physicalLawSelectionProvedIsFalse : physicalLawSelectionProved ≡ false
open MultiscaleWaveStatus public

currentMultiscaleWaveStatus : MultiscaleWaveStatus
currentMultiscaleWaveStatus =
  multiscale-wave-status
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
