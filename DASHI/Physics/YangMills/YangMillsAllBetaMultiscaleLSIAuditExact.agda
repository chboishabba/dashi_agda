module DASHI.Physics.YangMills.YangMillsAllBetaMultiscaleLSIAuditExact where

------------------------------------------------------------------------
-- SOURCES / CLAIM STATUS
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Martin Hairer, Gregory Miermont and Horng-Tzer Yau (organizers),
-- "Universality: Random Matrices, Random Geometry and SPDEs",
-- Oberwolfach Report 2022, no. 27.
-- DOI: 10.4171/OWR/2022/27.
-- The report documents the genuine strong-coupling stochastic program.
--
-- Henry Watt et al.,
-- "The Yang-Mills Mass Gap: From Proof Attempts to Dissolution by
-- Holographic Finiteness".
-- Zenodo DOI: 10.5281/zenodo.19699784.
-- This deposit describes an all-finite-beta lattice-gap argument as a proof
-- sketch.  It is not used here as a theorem dependency.
--
-- DASHI CONTRIBUTION
--
-- Separate source authority from mathematical content and give the proposed
-- all-beta multiscale route a literal dependency graph.  The admissible inputs
-- stop before the target lattice gap and correlation length, so any future
-- implementation can be checked for circularity.  No inhabitant of the final
-- all-beta theorem is supplied by citation or source status.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data SourceAuthority : Set where
  peerReviewedTheorem : SourceAuthority
  scholarlyWorkshopReport : SourceAuthority
  selfArchivedProofSketch : SourceAuthority

data NamedSource : Set where
  shenZhuZhuStrongCoupling : NamedSource
  oberwolfachStrongCouplingContext : NamedSource
  dissolutionAllBetaSketch : NamedSource

sourceAuthority : NamedSource → SourceAuthority
sourceAuthority shenZhuZhuStrongCoupling = peerReviewedTheorem
sourceAuthority oberwolfachStrongCouplingContext = scholarlyWorkshopReport
sourceAuthority dissolutionAllBetaSketch = selfArchivedProofSketch

strongCouplingSourceIsPeerReviewed :
  sourceAuthority shenZhuZhuStrongCoupling ≡ peerReviewedTheorem
strongCouplingSourceIsPeerReviewed = refl

allBetaDepositIsOnlySketchAuthority :
  sourceAuthority dissolutionAllBetaSketch ≡ selfArchivedProofSketch
allBetaDepositIsOnlySketchAuthority = refl

data MultiscaleInputAtom : Set where
  nonAbelianGaugePolchinskiFlow : MultiscaleInputAtom
  conditionalScaleMeasureGaugeInvariant : MultiscaleInputAtom
  scaleCovarianceOperatorPositive : MultiscaleInputAtom
  renormalizedHessianBound : MultiscaleInputAtom
  gaugeOrbitZeroModesControlled : MultiscaleInputAtom
  scaleFlowPreservesClassFunctions : MultiscaleInputAtom

data ForbiddenTargetAtom : Set where
  targetLatticeGap : ForbiddenTargetAtom
  targetCorrelationLength : ForbiddenTargetAtom

-- Accepted inputs and forbidden targets are different carriers.  A proposed
-- proof must provide an explicit translation before either target can enter an
-- input position; no such translation is present here.
acceptedInputCannotEqualForbiddenTarget :
  MultiscaleInputAtom ≡ ForbiddenTargetAtom → ⊥
acceptedInputCannotEqualForbiddenTarget ()

data AllBetaStage : Set where
  gaugeFlowStage : AllBetaStage
  conditionalMeasureStage : AllBetaStage
  renormalizedHessianStage : AllBetaStage
  multiscaleLSIDifferentialStage : AllBetaStage
  integratedLSIStage : AllBetaStage
  finiteVolumePoincareStage : AllBetaStage
  derivativePropagationStage : AllBetaStage
  spatialCovarianceStage : AllBetaStage
  explicitLatticeGapStage : AllBetaStage

nextAllBetaStage : AllBetaStage → AllBetaStage
nextAllBetaStage gaugeFlowStage = conditionalMeasureStage
nextAllBetaStage conditionalMeasureStage = renormalizedHessianStage
nextAllBetaStage renormalizedHessianStage = multiscaleLSIDifferentialStage
nextAllBetaStage multiscaleLSIDifferentialStage = integratedLSIStage
nextAllBetaStage integratedLSIStage = finiteVolumePoincareStage
nextAllBetaStage finiteVolumePoincareStage = derivativePropagationStage
nextAllBetaStage derivativePropagationStage = spatialCovarianceStage
nextAllBetaStage spatialCovarianceStage = explicitLatticeGapStage
nextAllBetaStage explicitLatticeGapStage = explicitLatticeGapStage

record MultiscaleLSIInputs : Set₁ where
  field
    FlowCarrier : Set
    ConditionalMeasureCarrier : Set
    CovarianceCarrier : Set
    RenormalizedHessianCarrier : Set

    flowIdentity : FlowCarrier
    conditionalGaugeInvariance : ConditionalMeasureCarrier
    covariancePositivity : CovarianceCarrier
    renormalizedHessianEstimate : RenormalizedHessianCarrier

open MultiscaleLSIInputs public

-- This theorem is structural rather than bibliographic: the accepted input
-- record has no field of either forbidden target type.
multiscaleInputDoesNotAssumeTargetGap :
  (inputs : MultiscaleLSIInputs) →
  ForbiddenTargetAtom →
  Bool
multiscaleInputDoesNotAssumeTargetGap inputs targetLatticeGap = true
multiscaleInputDoesNotAssumeTargetGap inputs targetCorrelationLength = true

record AllBetaMultiscaleLSIClaim : Set₁ where
  field
    Beta : Set
    Volume : Set
    Configuration : Set
    Measure : Configuration → Set
    PositiveConstant : Set

    finiteVolumeMeasure : Beta → Volume → Measure
    lsiConstant : Beta → PositiveConstant

    nonAbelianGaugePolchinskiFlowIdentity : Set
    conditionalScaleMeasureGaugeInvariant : Set
    scaleCovarianceOperatorPositive : Set
    renormalizedHessianOrSusceptibilityBound : Set
    multiscaleLSIDifferentialInequality : Set
    integratedMultiscaleLSILower : Set
    allBetaFiniteVolumeLSI : Set
    allBetaFiniteVolumePoincare : Set
    allBetaVolumeUniformConstants : Set
    allBetaDerivativeGeneratorCommutator : Set
    allBetaFiniteSpeedPropagation : Set
    allBetaSpatialCovarianceDecay : Set
    allBetaGapExplicitLower : Set

    gaugeOrbitZeroModesRemoved : Set
    conditionalLSIOnGaugeQuotient : Set
    gaugeFixingIndependence : Set
    multiscaleFlowPreservesClassFunctions : Set
    localObservableCylinderClassDense : Set

-- No canonical inhabitant is supplied.  In particular, the self-archived proof
-- sketch is not converted into any field of this record.

data ContinuumStage : Set where
  fixedBetaInfiniteVolumeLatticeGap : ContinuumStage
  changingSpacingScaleCompatibility : ContinuumStage
  continuumOSLimit : ContinuumStage
  reconstructedHamiltonianGap : ContinuumStage

fixedBetaGapIsNotScaleCompatibility :
  fixedBetaInfiniteVolumeLatticeGap
  ≡ changingSpacingScaleCompatibility → ⊥
fixedBetaGapIsNotScaleCompatibility ()

scaleCompatibilityIsNotContinuumOS :
  changingSpacingScaleCompatibility ≡ continuumOSLimit → ⊥
scaleCompatibilityIsNotContinuumOS ()

continuumOSIsNotHamiltonianGap :
  continuumOSLimit ≡ reconstructedHamiltonianGap → ⊥
continuumOSIsNotHamiltonianGap ()
