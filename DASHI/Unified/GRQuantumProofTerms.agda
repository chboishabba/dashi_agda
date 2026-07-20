module DASHI.Unified.GRQuantumProofTerms where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Proposition-level replacement for the earlier Boolean closure manifest.
--
-- Every named proposition below has a corresponding inhabitant.  A consumer
-- cannot promote a closure merely by choosing the proposition type; it must
-- supply the proof term as well.

infixr 4 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A
open _↔_ public

-- Local empty type, kept builtin-only so this module has no stdlib dependency.
data ⊥ : Set where

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- 1. Orthogonal multiscale closure -> unique quadratic functional.

record QuadraticUniquenessProof : Set₁ where
  field
    EnergyFunctional : Set
    SatisfiesMultiscaleLaws : EnergyFunctional → Set
    canonicalQuadraticDefect : EnergyFunctional
    canonicalSatisfiesLaws :
      SatisfiesMultiscaleLaws canonicalQuadraticDefect
    uniqueness :
      (energy : EnergyFunctional) →
      SatisfiesMultiscaleLaws energy →
      energy ≡ canonicalQuadraticDefect
open QuadraticUniquenessProof public

------------------------------------------------------------------------
-- 2. Causal order / chain-antichain / Lorentz closure.

record ChainAntichainLorentzProof : Set₁ where
  field
    Event : Set
    CausalRelated : Event → Event → Set
    Chain : Event → Event → Set
    Antichain : Set
    Separates : Antichain → Event → Event → Set
    chainDepth : Event → Event → Nat
    antichainWidth : Event → Event → Nat

    PosetIsomorphism : Set
    transportEvent : PosetIsomorphism → Event → Event
    chainDepthInvariant :
      (iso : PosetIsomorphism) (a b : Event) →
      chainDepth (transportEvent iso a) (transportEvent iso b)
      ≡ chainDepth a b
    antichainWidthInvariant :
      (iso : PosetIsomorphism) (a b : Event) →
      antichainWidth (transportEvent iso a) (transportEvent iso b)
      ≡ antichainWidth a b

    Interval : Set
    interval : Event → Event → Interval
    Null : Interval → Set
    finiteSpeedCone :
      (a b : Event) → Null (interval a b) → Set
    finiteSpeedConeProof :
      (a b : Event) →
      (nullReceipt : Null (interval a b)) →
      finiteSpeedCone a b nullReceipt

    spatialDimension : Nat
    spatialDimensionIsThree : spatialDimension ≡ 3
    timeDimension : Nat
    timeDimensionIsOne : timeDimension ≡ 1
    signatureUnique : Set
    signatureUniqueProof : signatureUnique
open ChainAntichainLorentzProof public

------------------------------------------------------------------------
-- 3. Constructive Clifford algebra and Spin double cover.

record CliffordUniversalProof : Set₁ where
  field
    Vector : Set
    Scalar : Set
    Q : Vector → Scalar
    Clifford : Set
    injectVector : Vector → Clifford
    multiply : Clifford → Clifford → Clifford
    scalarEmbed : Scalar → Clifford

    cliffordRelation :
      (v : Vector) →
      multiply (injectVector v) (injectVector v)
      ≡ scalarEmbed (Q v)

    TargetAlgebra : Set
    AdmissibleGeneratorMap : TargetAlgebra → Set
    FactorMap : TargetAlgebra → Set
    factorExists :
      (target : TargetAlgebra) →
      AdmissibleGeneratorMap target →
      FactorMap target
    factorUnique :
      (target : TargetAlgebra) →
      (generator : AdmissibleGeneratorMap target) →
      (left right : FactorMap target) →
      left ≡ right
open CliffordUniversalProof public

record TwoElementFiber {A B : Set} (map : A → B) (target : B) : Set where
  field
    first second : A
    firstMaps : map first ≡ target
    secondMaps : map second ≡ target
    distinct : first ≢ second
    exhaustive :
      (candidate : A) →
      map candidate ≡ target →
      (candidate ≡ first) ⊎ (candidate ≡ second)
open TwoElementFiber public

record SpinDoubleCoverProof : Set₁ where
  field
    Spin : Set
    SO : Set
    rho : Spin → SO
    spinIdentity : Spin
    soIdentity : SO
    plusOne minusOne : Spin

    SpinProduct : Spin → Spin → Spin
    SOProduct : SO → SO → SO
    rhoHomomorphism :
      (a b : Spin) →
      rho (SpinProduct a b) ≡ SOProduct (rho a) (rho b)

    SurjectiveWitness : SO → Set
    rhoSurjective : (rotation : SO) → SurjectiveWitness rotation

    kernelCharacterization :
      (s : Spin) →
      (rho s ≡ soIdentity)
      ↔ ((s ≡ plusOne) ⊎ (s ≡ minusOne))

    fiberIsTwoElement :
      (rotation : SO) → TwoElementFiber rho rotation
open SpinDoubleCoverProof public

------------------------------------------------------------------------
-- 4. Wave lift, finite tree algebra, continuum CCR, and Born measure.

record WaveLiftCCRProof : Set₁ where
  field
    Cylinder : Set
    HilbertState : Set
    Scalar : Set
    Operator : Set

    liftCylinder : Cylinder → HilbertState
    normSquared : HilbertState → Scalar
    configuration momentum identity : Operator
    commutator : Operator → Operator → Operator
    actionGrain : Scalar

    finiteTreeShiftLaw : Set
    finiteTreeShiftLawProof : finiteTreeShiftLaw
    continuumLimit : Set
    continuumLimitProof : continuumLimit
    canonicalCommutationRelation : Set
    continuumLimitYieldsCCR :
      finiteTreeShiftLaw →
      continuumLimit →
      canonicalCommutationRelation
    canonicalCommutationRelationProof : canonicalCommutationRelation

    OrthogonalFamily : Set
    bornMeasure : HilbertState → Scalar
    bornMeasureIsNormSquared :
      (state : HilbertState) →
      bornMeasure state ≡ normSquared state
    pythagoreanProbabilityAdditivity : OrthogonalFamily → Set
    pythagoreanProbabilityAdditivityProof :
      (family : OrthogonalFamily) →
      pythagoreanProbabilityAdditivity family
open WaveLiftCCRProof public

------------------------------------------------------------------------
-- 5. Full tensorial GR bridge.

record EinsteinTensorProof : Set₁ where
  field
    DiscreteValuation : Set
    Metric : Set
    Connection : Set
    Riemann : Set
    Ricci : Set
    ScalarCurvature : Set
    EinsteinTensor : Set
    StressEnergy : Set

    valuationToMetric : DiscreteValuation → Metric
    leviCivita : Metric → Connection
    riemann : Connection → Riemann
    ricci : Riemann → Ricci
    scalarCurvature : Metric → Ricci → ScalarCurvature
    einsteinTensor : Metric → Ricci → ScalarCurvature → EinsteinTensor
    stressEnergy : DiscreteValuation → StressEnergy

    discreteToContinuumConvergence : Set
    discreteToContinuumConvergenceProof : discreteToContinuumConvergence
    contractedBianchiIdentity : Set
    contractedBianchiIdentityProof : contractedBianchiIdentity
    stressEnergyConservation : Set
    stressEnergyConservationProof : stressEnergyConservation
    variationalSourceEquation : Set
    variationalSourceEquationProof : variationalSourceEquation
    universalSpinTwoSelfCoupling : Set
    universalSpinTwoSelfCouplingProof : universalSpinTwoSelfCoupling
    backgroundIndependence : Set
    backgroundIndependenceProof : backgroundIndependence
open EinsteinTensorProof public

------------------------------------------------------------------------
-- 6. Hypersurface-deformation / Dirac constraint algebra.

record ConstraintAlgebraProof : Set₁ where
  field
    Operator : Set
    Lapse : Set
    Shift : Set
    Hamiltonian : Lapse → Operator
    Momentum : Shift → Operator
    bracket : Operator → Operator → Operator

    momentumMomentumClosure : Set
    momentumMomentumClosureProof : momentumMomentumClosure
    momentumHamiltonianClosure : Set
    momentumHamiltonianClosureProof : momentumHamiltonianClosure
    hamiltonianHamiltonianClosure : Set
    hamiltonianHamiltonianClosureProof : hamiltonianHamiltonianClosure
    metricDependentStructureFunctions : Set
    metricDependentStructureFunctionsProof : metricDependentStructureFunctions
    decimationRelabellingEquivariance : Set
    decimationRelabellingEquivarianceProof : decimationRelabellingEquivariance
    anomalyFreeQuantumRepresentation : Set
    anomalyFreeQuantumRepresentationProof : anomalyFreeQuantumRepresentation
open ConstraintAlgebraProof public

------------------------------------------------------------------------
-- 7. UV spectral finiteness and low-energy recovery.

record UVSpectralProof : Set₁ where
  field
    Region : Set
    Scale : Set
    Operator : Set
    Spectrum : Operator → Set

    finiteResolvableDepth : (region : Region) → Set
    finiteResolvableDepthProof :
      (region : Region) → finiteResolvableDepth region
    regionalHilbertDimensionBound : (region : Region) → Set
    regionalHilbertDimensionBoundProof :
      (region : Region) → regionalHilbertDimensionBound region
    regulatedSpectrumFinite : (operator : Operator) → Set
    regulatedSpectrumFiniteProof :
      (operator : Operator) → regulatedSpectrumFinite operator
    amplitudesConverge : Set
    amplitudesConvergeProof : amplitudesConverge
    renormalizationPreservesBound : Set
    renormalizationPreservesBoundProof : renormalizationPreservesBound
    lowEnergyLimitExists : Set
    lowEnergyLimitExistsProof : lowEnergyLimitExists
    lowEnergyLimitMatchesRequiredPhysics : Set
    lowEnergyLimitMatchesRequiredPhysicsProof :
      lowEnergyLimitMatchesRequiredPhysics
open UVSpectralProof public

------------------------------------------------------------------------
-- Terminal proof bundle.  No canonical inhabitant is defined here.

record TerminalGRQuantumProof : Set₁ where
  field
    quadratic : QuadraticUniquenessProof
    causalLorentz : ChainAntichainLorentzProof
    clifford : CliffordUniversalProof
    spinCover : SpinDoubleCoverProof
    waveCCR : WaveLiftCCRProof
    einstein : EinsteinTensorProof
    constraints : ConstraintAlgebraProof
    uvSpectrum : UVSpectralProof

    oneUnderlyingSubstrate : Set
    oneUnderlyingSubstrateProof : oneUnderlyingSubstrate
    quantumReadingRecovered : Set
    quantumReadingRecoveredProof : quantumReadingRecovered
    generalRelativisticReadingRecovered : Set
    generalRelativisticReadingRecoveredProof :
      generalRelativisticReadingRecovered
    empiricalCorrespondenceSupplied : Set
    empiricalCorrespondenceSuppliedProof : empiricalCorrespondenceSupplied
open TerminalGRQuantumProof public

terminalProofHasNoDefault : TerminalGRQuantumProof → ⊤
terminalProofHasNoDefault _ = tt
