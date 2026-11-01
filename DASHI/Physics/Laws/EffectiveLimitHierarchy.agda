module DASHI.Physics.Laws.EffectiveLimitHierarchy where

open import DASHI.Physics.Laws.PhysicalLawCore

-- Laws at different scales are connected by controlled limit, quotient, or
-- renormalisation maps.  Agreement of labels or qualitative behaviour is not a
-- proof that one law has been derived from another.
data LimitKind : Set where
  discreteToContinuum      : LimitKind
  relativisticToNewtonian  : LimitKind
  quantumToClassical       : LimitKind
  microscopicToThermodynamic : LimitKind
  kineticToFluid           : LimitKind
  waveToRay                : LimitKind
  fieldToParticle          : LimitKind
  gaugeToEffectiveInteraction : LimitKind
  atomicToMolecular        : LimitKind
  molecularToContinuum     : LimitKind
  ultravioletToInfrared    : LimitKind

data LimitStatus : Set where
  exactCommutingBridge : LimitStatus
  quantifiedApproximation : LimitStatus
  compactnessSubsequenceBridge : LimitStatus
  formalAsymptoticOnly : LimitStatus
  empiricalEffectiveMatch : LimitStatus
  openLimitProblem : LimitStatus

record LawScaleMap
  (fine coarse : PhysicalLawSurface) : Set₁ where
  field
    Scale       : Set
    FineState   : Set
    CoarseState : Set
    Error       : Set

    encodeFine  : PhysicalLawSurface.State fine → FineState
    decodeCoarse : CoarseState → PhysicalLawSurface.State coarse
    coarseGrain : Scale → FineState → CoarseState
    approximationError : Scale → FineState → Error
    Controlled  : Error → Set

    domainCompatible : Set
    observableCompatible : Set
    evolutionCompatible : Set

record RenormalisationGroupLaw : Set₁ where
  field
    Theory      : Set
    Scale       : Set
    Coupling    : Set
    EffectiveAction : Set
    FixedPoint  : Set
    RelevantOperator : Set
    IrrelevantOperator : Set

    coarseGrain      : Scale → Theory → Theory
    runningCoupling  : Scale → Theory → Coupling
    effectiveAction  : Scale → Theory → EffectiveAction
    fixedPoint       : Theory → FixedPoint → Set
    relevant         : Theory → RelevantOperator → Set
    irrelevant       : Theory → IrrelevantOperator → Set

    semigroupLaw     : Scale → Scale → Theory → Set
    universalityClass : Theory → Theory → Set

record ContinuumLimitBoundary : Set₁ where
  field
    DiscreteState  : Set
    ContinuumState : Set
    Resolution     : Set
    Norm           : Set
    Error          : Set

    interpolate    : Resolution → DiscreteState → ContinuumState
    error          : Resolution → DiscreteState → Error
    Controlled     : Norm → Error → Set
    Consistent     : Resolution → Set
    Stable         : Resolution → Set
    Compact        : Resolution → Set

record EffectiveFieldTheoryLaw : Set₁ where
  field
    Field          : Set
    Operator       : Set
    Scale          : Set
    Coefficient    : Set
    Action         : Set
    ErrorOrder     : Set

    coefficientAt  : Scale → Operator → Coefficient
    truncatedAction : Scale → Action
    truncationError : Scale → ErrorOrder
    SymmetryAllowed : Operator → Set
    PowerCounting   : Operator → Set
    ValidBelowCutoff : Scale → Set

record EmergentLawBoundary : Set₁ where
  field
    MicroscopicState : Set
    MacroObservable  : Set
    OrderParameter   : Set
    Phase            : Set
    CoarseGraining   : Set

    observeMacro : CoarseGraining → MicroscopicState → MacroObservable
    orderParameter : MacroObservable → OrderParameter
    phaseOf        : OrderParameter → Phase
    RobustUnderMicroscopicVariation : Phase → Set

record LimitHierarchyAuthorityBoundary : Set₁ where
  field
    asymptoticExpansionIsNotConvergence : Set
    pointwiseConvergenceIsNotUniformControl : Set
    compactnessIsNotUniqueness : Set
    numericalAgreementIsNotDerivation : Set
    renormalisationFlowRequiresDefinedTheorySpace : Set
    universalityRequiresRelevantOperatorControl : Set
    effectiveLawHasFiniteValidityDomain : Set
    emergenceDoesNotEraseMicroscopicConstraints : Set
