module DASHI.Physics.Closure.ConstraintRenormalizationLowEnergy where

open import Agda.Builtin.Nat using (Nat)

import DASHI.Unified.GRQuantumProofTerms as Legacy
import DASHI.Empirical.GRQuantumEmpiricalValidationProgramme as Empirical

------------------------------------------------------------------------
-- Nontrivial metric-dependent hypersurface-deformation representation.

record MetricDependentConstraintAuthority : Set₁ where
  field
    SpatialMetric : Set
    CanonicalState : Set
    Lapse : Set
    Shift : Set

    ClassicalConstraint : Set
    hamiltonianConstraint :
      SpatialMetric → Lapse → CanonicalState → ClassicalConstraint
    momentumConstraint :
      SpatialMetric → Shift → CanonicalState → ClassicalConstraint
    classicalBracket :
      ClassicalConstraint → ClassicalConstraint → ClassicalConstraint
    MetricStructureFunction : Set
    inverseMetricStructureFunction :
      SpatialMetric → Lapse → Lapse → MetricStructureFunction

    classicalMomentumMomentumClosure : Set
    classicalMomentumMomentumClosureProof :
      classicalMomentumMomentumClosure
    classicalMomentumHamiltonianClosure : Set
    classicalMomentumHamiltonianClosureProof :
      classicalMomentumHamiltonianClosure
    classicalHamiltonianHamiltonianClosureWithMetricStructureFunction : Set
    classicalHamiltonianHamiltonianClosureWithMetricStructureFunctionProof :
      classicalHamiltonianHamiltonianClosureWithMetricStructureFunction

    HilbertState : Set
    DenseInvariantDomain : Set
    QuantumOperator : Set
    quantizeHamiltonian : SpatialMetric → Lapse → QuantumOperator
    quantizeMomentum : SpatialMetric → Shift → QuantumOperator
    regulatedCommutator : QuantumOperator → QuantumOperator → QuantumOperator
    quantumStructureFunctionOperator :
      SpatialMetric → MetricStructureFunction → QuantumOperator

    commonDenseDomainPreserved : Set
    commonDenseDomainPreservedProof : commonDenseDomainPreserved
    operatorOrderingDeclared : Set
    operatorOrderingDeclaredProof : operatorOrderingDeclared
    regulatorRemovedOnDomain : Set
    regulatorRemovedOnDomainProof : regulatorRemovedOnDomain
    quantumCommutatorsRepresentClassicalBrackets : Set
    quantumCommutatorsRepresentClassicalBracketsProof :
      quantumCommutatorsRepresentClassicalBrackets

    AnomalyCocycle : Set
    anomaly : AnomalyCocycle
    zeroAnomaly : AnomalyCocycle
    anomalyVanishes : Set
    anomalyVanishesProof : anomalyVanishes
    jacobiIdentityOnPhysicalDomain : Set
    jacobiIdentityOnPhysicalDomainProof : jacobiIdentityOnPhysicalDomain
    diffeomorphismEquivariance : Set
    diffeomorphismEquivarianceProof : diffeomorphismEquivariance
    nontrivialMetricDependence : Set
    nontrivialMetricDependenceProof : nontrivialMetricDependence

    legacySurface : Legacy.ConstraintAlgebraProof
    legacyClosed : Legacy.ConstraintAlgebraClosed legacySurface
    legacyStructureFunctionsAgree : Set
    legacyStructureFunctionsAgreeProof : legacyStructureFunctionsAgree
open MetricDependentConstraintAuthority public

------------------------------------------------------------------------
-- Renormalized amplitude convergence.

record RenormalizedAmplitudeConvergenceAuthority : Set₁ where
  field
    Regulator : Set
    RenormalizationScheme : Set
    ExternalData : Set
    BareAmplitude : Set
    Counterterm : Set
    RenormalizedAmplitude : Set
    LimitAmplitude : Set

    bareAmplitude : Regulator → ExternalData → BareAmplitude
    counterterm :
      RenormalizationScheme → Regulator → ExternalData → Counterterm
    renormalize : BareAmplitude → Counterterm → RenormalizedAmplitude
    renormalizedAt :
      RenormalizationScheme → Regulator → ExternalData → RenormalizedAmplitude
    limitAmplitude : ExternalData → LimitAmplitude

    Convergence : RenormalizedAmplitude → LimitAmplitude → Set
    RegulatorSequence : Set
    regulatorTerm : RegulatorSequence → Nat → Regulator

    subdivergencesSubtractedRecursively : Set
    subdivergencesSubtractedRecursivelyProof :
      subdivergencesSubtractedRecursively
    countertermsLocalAndSymmetryCompatible : Set
    countertermsLocalAndSymmetryCompatibleProof :
      countertermsLocalAndSymmetryCompatible
    renormalizedFamilyCauchy : Set
    renormalizedFamilyCauchyProof : renormalizedFamilyCauchy
    amplitudesConverge :
      (scheme : RenormalizationScheme) →
      (sequence : RegulatorSequence) →
      (external : ExternalData) →
      Set
    amplitudesConvergeProof :
      (scheme : RenormalizationScheme) →
      (sequence : RegulatorSequence) →
      (external : ExternalData) →
      amplitudesConverge scheme sequence external
    limitIndependentOfAdmissibleRegulator : Set
    limitIndependentOfAdmissibleRegulatorProof :
      limitIndependentOfAdmissibleRegulator
    schemesRelatedByFiniteRenormalization : Set
    schemesRelatedByFiniteRenormalizationProof :
      schemesRelatedByFiniteRenormalization
    wardOrBRSTIdentitiesSurviveLimit : Set
    wardOrBRSTIdentitiesSurviveLimitProof :
      wardOrBRSTIdentitiesSurviveLimit
    unitarityOrReflectionPositivitySurvivesLimit : Set
    unitarityOrReflectionPositivitySurvivesLimitProof :
      unitarityOrReflectionPositivitySurvivesLimit
    compositionAndFactorizationSurviveLimit : Set
    compositionAndFactorizationSurviveLimitProof :
      compositionAndFactorizationSurviveLimit

    legacyUVSurface : Legacy.UVSpectralProof
    legacyUVClosed : Legacy.UVSpectralClosed legacyUVSurface
    legacyAmplitudeConvergenceAgrees : Set
    legacyAmplitudeConvergenceAgreesProof :
      legacyAmplitudeConvergenceAgrees
open RenormalizedAmplitudeConvergenceAuthority public

------------------------------------------------------------------------
-- Physically correct low-energy GR/QFT recovery.

record PhysicalLowEnergyGRQFTRecoveryAuthority : Set₁ where
  field
    MicroscopicState : Set
    EnergyScale : Set
    EffectiveField : Set
    EffectiveAction : Set
    GRReference : Set
    QFTReference : Set
    Observable : Set
    PhysicalConstant : Set
    ErrorBudget : Set

    coarseGrain : EnergyScale → MicroscopicState → EffectiveField
    effectiveAction : EnergyScale → EffectiveField → EffectiveAction
    grReferenceAt : EnergyScale → GRReference
    qftReferenceAt : EnergyScale → QFTReference
    dashiObservable : EnergyScale → EffectiveField → Observable
    grObservable : GRReference → Observable
    qftObservable : QFTReference → Observable

    lowEnergySequence : Set
    scaleTerm : lowEnergySequence → Nat → EnergyScale
    asymptoticError : lowEnergySequence → Nat → ErrorBudget

    irrelevantOperatorsDecouple : Set
    irrelevantOperatorsDecoupleProof : irrelevantOperatorsDecouple
    relevantAndMarginalCouplingsRenormalized : Set
    relevantAndMarginalCouplingsRenormalizedProof :
      relevantAndMarginalCouplingsRenormalized
    dimensionfulConstantsMatched : Set
    dimensionfulConstantsMatchedProof : dimensionfulConstantsMatched
    equivalencePrincipleAndUniversalCouplingRecovered : Set
    equivalencePrincipleAndUniversalCouplingRecoveredProof :
      equivalencePrincipleAndUniversalCouplingRecovered
    einsteinHilbertLeadingActionRecovered : Set
    einsteinHilbertLeadingActionRecoveredProof :
      einsteinHilbertLeadingActionRecovered
    standardFreeAndInteractingQFTRecovered : Set
    standardFreeAndInteractingQFTRecoveredProof :
      standardFreeAndInteractingQFTRecovered
    qftOnCurvedSpacetimeRecovered : Set
    qftOnCurvedSpacetimeRecoveredProof :
      qftOnCurvedSpacetimeRecovered
    semiclassicalBackreactionRecovered : Set
    semiclassicalBackreactionRecoveredProof :
      semiclassicalBackreactionRecovered
    scatteringAndCorrelationFunctionsMatch : Set
    scatteringAndCorrelationFunctionsMatchProof :
      scatteringAndCorrelationFunctionsMatch
    errorsVanishInDeclaredLowEnergyLimit : Set
    errorsVanishInDeclaredLowEnergyLimitProof :
      errorsVanishInDeclaredLowEnergyLimit
    noEvaluationDataUsedToDefineLimit : Set
    noEvaluationDataUsedToDefineLimitProof :
      noEvaluationDataUsedToDefineLimit

    legacyUVSurface : Legacy.UVSpectralProof
    legacyUVClosed : Legacy.UVSpectralClosed legacyUVSurface
    empiricalCorrespondence :
      Empirical.StrictPhysicalGRQuantumCorrespondence
    lowEnergySurfaceAgreesWithAcceptedLimitSuite : Set
    lowEnergySurfaceAgreesWithAcceptedLimitSuiteProof :
      lowEnergySurfaceAgreesWithAcceptedLimitSuite
    predictionDerivedFromFrozenLowEnergyTheory : Set
    predictionDerivedFromFrozenLowEnergyTheoryProof :
      predictionDerivedFromFrozenLowEnergyTheory
open PhysicalLowEnergyGRQFTRecoveryAuthority public

lowEnergyEmpiricalAuthority :
  PhysicalLowEnergyGRQFTRecoveryAuthority →
  Empirical.StrictPhysicalGRQuantumCorrespondence
lowEnergyEmpiricalAuthority = empiricalCorrespondence
