module DASHI.Unified.GRQuantumProofTerms where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Proposition-level replacement for the earlier Boolean closure manifest.
--
-- Each theorem surface is separated from an inhabited `Closed` record.  This
-- lets finite or conditional models state their proposition language without
-- pretending that merely naming a `Set` proves it.  Terminal promotion requires
-- both the surface and the corresponding closure witness.

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

data ⊥ : Set where

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- 1. Orthogonal multiscale closure -> unique quadratic functional.
-- This record already contains the proof terms directly.

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

    spatialDimension : Nat
    spatialDimensionIsThree : spatialDimension ≡ 3
    timeDimension : Nat
    timeDimensionIsOne : timeDimension ≡ 1
    signatureUnique : Set
open ChainAntichainLorentzProof public

record ChainAntichainLorentzClosed
  (surface : ChainAntichainLorentzProof) : Set where
  open ChainAntichainLorentzProof surface
  field
    finiteSpeedConeProof :
      (a b : Event) →
      (nullReceipt : Null (interval a b)) →
      finiteSpeedCone a b nullReceipt
    signatureUniqueProof : signatureUnique
open ChainAntichainLorentzClosed public

------------------------------------------------------------------------
-- 3. Constructive Clifford algebra and Spin double cover.
-- These records already carry equations and witnesses rather than proposition
-- names alone.

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
    continuumLimit : Set
    canonicalCommutationRelation : Set
    continuumLimitYieldsCCR :
      finiteTreeShiftLaw →
      continuumLimit →
      canonicalCommutationRelation

    OrthogonalFamily : Set
    bornMeasure : HilbertState → Scalar
    bornMeasureIsNormSquared :
      (state : HilbertState) →
      bornMeasure state ≡ normSquared state
    pythagoreanProbabilityAdditivity : OrthogonalFamily → Set
open WaveLiftCCRProof public

record WaveLiftCCRClosed (surface : WaveLiftCCRProof) : Set where
  open WaveLiftCCRProof surface
  field
    finiteTreeShiftLawProof : finiteTreeShiftLaw
    continuumLimitProof : continuumLimit
    canonicalCommutationRelationProof : canonicalCommutationRelation
    pythagoreanProbabilityAdditivityProof :
      (family : OrthogonalFamily) →
      pythagoreanProbabilityAdditivity family
open WaveLiftCCRClosed public

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
    contractedBianchiIdentity : Set
    stressEnergyConservation : Set
    variationalSourceEquation : Set
    universalSpinTwoSelfCoupling : Set
    backgroundIndependence : Set
open EinsteinTensorProof public

record EinsteinTensorClosed (surface : EinsteinTensorProof) : Set where
  open EinsteinTensorProof surface
  field
    discreteToContinuumConvergenceProof : discreteToContinuumConvergence
    contractedBianchiIdentityProof : contractedBianchiIdentity
    stressEnergyConservationProof : stressEnergyConservation
    variationalSourceEquationProof : variationalSourceEquation
    universalSpinTwoSelfCouplingProof : universalSpinTwoSelfCoupling
    backgroundIndependenceProof : backgroundIndependence
open EinsteinTensorClosed public

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
    momentumHamiltonianClosure : Set
    hamiltonianHamiltonianClosure : Set
    metricDependentStructureFunctions : Set
    decimationRelabellingEquivariance : Set
    anomalyFreeQuantumRepresentation : Set
open ConstraintAlgebraProof public

record ConstraintAlgebraClosed (surface : ConstraintAlgebraProof) : Set where
  open ConstraintAlgebraProof surface
  field
    momentumMomentumClosureProof : momentumMomentumClosure
    momentumHamiltonianClosureProof : momentumHamiltonianClosure
    hamiltonianHamiltonianClosureProof : hamiltonianHamiltonianClosure
    metricDependentStructureFunctionsProof : metricDependentStructureFunctions
    decimationRelabellingEquivarianceProof : decimationRelabellingEquivariance
    anomalyFreeQuantumRepresentationProof : anomalyFreeQuantumRepresentation
open ConstraintAlgebraClosed public

------------------------------------------------------------------------
-- 7. UV spectral finiteness and low-energy recovery.

record UVSpectralProof : Set₁ where
  field
    Region : Set
    Scale : Set
    Operator : Set
    Spectrum : Operator → Set

    finiteResolvableDepth : (region : Region) → Set
    regionalHilbertDimensionBound : (region : Region) → Set
    regulatedSpectrumFinite : (operator : Operator) → Set
    amplitudesConverge : Set
    renormalizationPreservesBound : Set
    lowEnergyLimitExists : Set
    lowEnergyLimitMatchesRequiredPhysics : Set
open UVSpectralProof public

record UVSpectralClosed (surface : UVSpectralProof) : Set where
  open UVSpectralProof surface
  field
    finiteResolvableDepthProof :
      (region : Region) → finiteResolvableDepth region
    regionalHilbertDimensionBoundProof :
      (region : Region) → regionalHilbertDimensionBound region
    regulatedSpectrumFiniteProof :
      (operator : Operator) → regulatedSpectrumFinite operator
    amplitudesConvergeProof : amplitudesConverge
    renormalizationPreservesBoundProof : renormalizationPreservesBound
    lowEnergyLimitExistsProof : lowEnergyLimitExists
    lowEnergyLimitMatchesRequiredPhysicsProof :
      lowEnergyLimitMatchesRequiredPhysics
open UVSpectralClosed public

------------------------------------------------------------------------
-- Terminal proof bundle.  No canonical inhabitant is defined here.

record TerminalGRQuantumProof : Set₁ where
  field
    quadratic : QuadraticUniquenessProof

    causalLorentz : ChainAntichainLorentzProof
    causalLorentzClosed : ChainAntichainLorentzClosed causalLorentz

    clifford : CliffordUniversalProof
    spinCover : SpinDoubleCoverProof

    waveCCR : WaveLiftCCRProof
    waveCCRClosed : WaveLiftCCRClosed waveCCR

    einstein : EinsteinTensorProof
    einsteinClosed : EinsteinTensorClosed einstein

    constraints : ConstraintAlgebraProof
    constraintsClosed : ConstraintAlgebraClosed constraints

    uvSpectrum : UVSpectralProof
    uvSpectrumClosed : UVSpectralClosed uvSpectrum

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
