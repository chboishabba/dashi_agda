module DASHI.Core.FormalLensVocabularyCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Normalized formal-lens vocabulary.
--
-- This module is a reusable taxonomy layer, not a one-core-per-word
-- qualification bundle.  It keeps the vocabulary broad, concrete, and
-- candidate-only.

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

------------------------------------------------------------------------
-- Families.

data FormalLensFamily : Set where
  Algebraic :
    FormalLensFamily

  Categorical :
    FormalLensFamily

  Logical :
    FormalLensFamily

  OrderTheoretic :
    FormalLensFamily

  GraphTheoretic :
    FormalLensFamily

  Ontological :
    FormalLensFamily

  ProvenanceTheoretic :
    FormalLensFamily

  Topological :
    FormalLensFamily

  Geometric :
    FormalLensFamily

  NumberTheoretic :
    FormalLensFamily

  Dynamical :
    FormalLensFamily

  OperatorTheoretic :
    FormalLensFamily

  InformationTheoretic :
    FormalLensFamily

  StatisticalFamily :
    FormalLensFamily

  DecisionTheoretic :
    FormalLensFamily

  CryptographicFamily :
    FormalLensFamily

  GovernanceTheoretic :
    FormalLensFamily

  SymbolicRationalFamily :
    FormalLensFamily

  NamedFormalLensFamily :
    String →
    FormalLensFamily

------------------------------------------------------------------------
-- Kinds.

data FormalLensKind : Set where
  Algebra :
    FormalLensKind

  GeneratedAlgebra :
    FormalLensKind

  UniversalAlgebra :
    FormalLensKind

  QuadraticCarrier :
    FormalLensKind

  GradedAlgebra :
    FormalLensKind

  OperatorAlgebra :
    FormalLensKind

  VertexAlgebra :
    FormalLensKind

  Group :
    FormalLensKind

  Semigroup :
    FormalLensKind

  Monoid :
    FormalLensKind

  Representation :
    FormalLensKind

  SymmetryAction :
    FormalLensKind

  InvariantTheory :
    FormalLensKind

  FixedPoint :
    FormalLensKind

  Category :
    FormalLensKind

  HigherCategory :
    FormalLensKind

  Operad :
    FormalLensKind

  Topos :
    FormalLensKind

  Logic :
    FormalLensKind

  TypeTheory :
    FormalLensKind

  Proof :
    FormalLensKind

  Certificate :
    FormalLensKind

  Order :
    FormalLensKind

  Lattice :
    FormalLensKind

  Graph :
    FormalLensKind

  Hypergraph :
    FormalLensKind

  Ontology :
    FormalLensKind

  DescriptionLogic :
    FormalLensKind

  Provenance :
    FormalLensKind

  Topology :
    FormalLensKind

  AlgebraicTopology :
    FormalLensKind

  Homotopy :
    FormalLensKind

  Homology :
    FormalLensKind

  Cohomology :
    FormalLensKind

  FiberBundle :
    FormalLensKind

  Fibration :
    FormalLensKind

  Sheaf :
    FormalLensKind

  Cosheaf :
    FormalLensKind

  KTheory :
    FormalLensKind

  StableStructure :
    FormalLensKind

  PeriodicRecurrence :
    FormalLensKind

  Obstruction :
    FormalLensKind

  SpectralSequence :
    FormalLensKind

  FiberClassification :
    FormalLensKind

  Geometry :
    FormalLensKind

  DifferentialGeometry :
    FormalLensKind

  AlgebraicGeometry :
    FormalLensKind

  Manifold :
    FormalLensKind

  LieTheory :
    FormalLensKind

  SpinGeometry :
    FormalLensKind

  Number :
    FormalLensKind

  Arithmetic :
    FormalLensKind

  Valuation :
    FormalLensKind

  PrimeDecomposition :
    FormalLensKind

  LocalGlobal :
    FormalLensKind

  Modular :
    FormalLensKind

  Automorphic :
    FormalLensKind

  TransitionSystem :
    FormalLensKind

  RewriteDynamics :
    FormalLensKind

  DynamicalSystem :
    FormalLensKind

  Control :
    FormalLensKind

  Automaton :
    FormalLensKind

  FormalLanguage :
    FormalLensKind

  Operator :
    FormalLensKind

  Functional :
    FormalLensKind

  Hamiltonian :
    FormalLensKind

  Lyapunov :
    FormalLensKind

  GradientFlow :
    FormalLensKind

  Optimization :
    FormalLensKind

  Information :
    FormalLensKind

  Entropy :
    FormalLensKind

  Probability :
    FormalLensKind

  Statistical :
    FormalLensKind

  Inference :
    FormalLensKind

  Estimator :
    FormalLensKind

  HypothesisTest :
    FormalLensKind

  ConfidenceInterval :
    FormalLensKind

  RobustStatistic :
    FormalLensKind

  OutlierDetection :
    FormalLensKind

  Sampling :
    FormalLensKind

  ExperimentalDesign :
    FormalLensKind

  DecisionTheory :
    FormalLensKind

  Bayesian :
    FormalLensKind

  Frequentist :
    FormalLensKind

  CausalInference :
    FormalLensKind

  UncertaintyQuantification :
    FormalLensKind

  ModelSelection :
    FormalLensKind

  InformationCriterion :
    FormalLensKind

  Risk :
    FormalLensKind

  Reliability :
    FormalLensKind

  ExtremeValue :
    FormalLensKind

  TimeSeries :
    FormalLensKind

  StochasticProcess :
    FormalLensKind

  Cryptographic :
    FormalLensKind

  TrapdoorProjection :
    FormalLensKind

  SecretWitness :
    FormalLensKind

  QuotientResidue :
    FormalLensKind

  HiddenLift :
    FormalLensKind

  Commitment :
    FormalLensKind

  Governance :
    FormalLensKind

  SymbolicRational :
    FormalLensKind

  NamedFormalLensKind :
    String →
    FormalLensKind

------------------------------------------------------------------------
-- Family projection.

familyOf : FormalLensKind → FormalLensFamily
familyOf Algebra = Algebraic
familyOf GeneratedAlgebra = Algebraic
familyOf UniversalAlgebra = Algebraic
familyOf QuadraticCarrier = Algebraic
familyOf GradedAlgebra = Algebraic
familyOf OperatorAlgebra = Algebraic
familyOf VertexAlgebra = Algebraic
familyOf Group = Algebraic
familyOf Semigroup = Algebraic
familyOf Monoid = Algebraic
familyOf Representation = Algebraic
familyOf SymmetryAction = Algebraic
familyOf InvariantTheory = Algebraic
familyOf FixedPoint = Dynamical
familyOf Category = Categorical
familyOf HigherCategory = Categorical
familyOf Operad = Categorical
familyOf Topos = Categorical
familyOf Logic = Logical
familyOf TypeTheory = Logical
familyOf Proof = Logical
familyOf Certificate = Logical
familyOf Order = OrderTheoretic
familyOf Lattice = OrderTheoretic
familyOf Graph = GraphTheoretic
familyOf Hypergraph = GraphTheoretic
familyOf Ontology = Ontological
familyOf DescriptionLogic = Logical
familyOf Provenance = ProvenanceTheoretic
familyOf Topology = Topological
familyOf AlgebraicTopology = Topological
familyOf Homotopy = Topological
familyOf Homology = Topological
familyOf Cohomology = Topological
familyOf FiberBundle = Topological
familyOf Fibration = Topological
familyOf Sheaf = Topological
familyOf Cosheaf = Topological
familyOf KTheory = Topological
familyOf StableStructure = Topological
familyOf PeriodicRecurrence = Dynamical
familyOf Obstruction = Topological
familyOf SpectralSequence = Topological
familyOf FiberClassification = Topological
familyOf Geometry = Geometric
familyOf DifferentialGeometry = Geometric
familyOf AlgebraicGeometry = Geometric
familyOf Manifold = Geometric
familyOf LieTheory = Geometric
familyOf SpinGeometry = Geometric
familyOf Number = NumberTheoretic
familyOf Arithmetic = NumberTheoretic
familyOf Valuation = NumberTheoretic
familyOf PrimeDecomposition = NumberTheoretic
familyOf LocalGlobal = NumberTheoretic
familyOf Modular = NumberTheoretic
familyOf Automorphic = NumberTheoretic
familyOf TransitionSystem = Dynamical
familyOf RewriteDynamics = Dynamical
familyOf DynamicalSystem = Dynamical
familyOf Control = Dynamical
familyOf Automaton = Dynamical
familyOf FormalLanguage = Dynamical
familyOf Operator = OperatorTheoretic
familyOf Functional = OperatorTheoretic
familyOf Hamiltonian = OperatorTheoretic
familyOf Lyapunov = Dynamical
familyOf GradientFlow = Dynamical
familyOf Optimization = DecisionTheoretic
familyOf Information = InformationTheoretic
familyOf Entropy = InformationTheoretic
familyOf Probability = InformationTheoretic
familyOf Statistical = StatisticalFamily
familyOf Inference = InformationTheoretic
familyOf Estimator = StatisticalFamily
familyOf HypothesisTest = StatisticalFamily
familyOf ConfidenceInterval = StatisticalFamily
familyOf RobustStatistic = StatisticalFamily
familyOf OutlierDetection = StatisticalFamily
familyOf Sampling = InformationTheoretic
familyOf ExperimentalDesign = DecisionTheoretic
familyOf DecisionTheory = DecisionTheoretic
familyOf Bayesian = StatisticalFamily
familyOf Frequentist = StatisticalFamily
familyOf CausalInference = DecisionTheoretic
familyOf UncertaintyQuantification = InformationTheoretic
familyOf ModelSelection = DecisionTheoretic
familyOf InformationCriterion = InformationTheoretic
familyOf Risk = DecisionTheoretic
familyOf Reliability = StatisticalFamily
familyOf ExtremeValue = StatisticalFamily
familyOf TimeSeries = StatisticalFamily
familyOf StochasticProcess = StatisticalFamily
familyOf Cryptographic = CryptographicFamily
familyOf TrapdoorProjection = CryptographicFamily
familyOf SecretWitness = CryptographicFamily
familyOf QuotientResidue = CryptographicFamily
familyOf HiddenLift = CryptographicFamily
familyOf Commitment = CryptographicFamily
familyOf Governance = GovernanceTheoretic
familyOf SymbolicRational = SymbolicRationalFamily
familyOf (NamedFormalLensKind name) = NamedFormalLensFamily name

------------------------------------------------------------------------
-- Canonical lists.

canonicalFormalLensKinds : List FormalLensKind
canonicalFormalLensKinds =
  Algebra
  ∷ GeneratedAlgebra
  ∷ UniversalAlgebra
  ∷ QuadraticCarrier
  ∷ GradedAlgebra
  ∷ OperatorAlgebra
  ∷ VertexAlgebra
  ∷ Group
  ∷ Semigroup
  ∷ Monoid
  ∷ Representation
  ∷ SymmetryAction
  ∷ InvariantTheory
  ∷ FixedPoint
  ∷ Category
  ∷ HigherCategory
  ∷ Operad
  ∷ Topos
  ∷ Logic
  ∷ TypeTheory
  ∷ Proof
  ∷ Certificate
  ∷ Order
  ∷ Lattice
  ∷ Graph
  ∷ Hypergraph
  ∷ Ontology
  ∷ DescriptionLogic
  ∷ Provenance
  ∷ Topology
  ∷ AlgebraicTopology
  ∷ Homotopy
  ∷ Homology
  ∷ Cohomology
  ∷ FiberBundle
  ∷ Fibration
  ∷ Sheaf
  ∷ Cosheaf
  ∷ KTheory
  ∷ StableStructure
  ∷ PeriodicRecurrence
  ∷ Obstruction
  ∷ SpectralSequence
  ∷ FiberClassification
  ∷ Geometry
  ∷ DifferentialGeometry
  ∷ AlgebraicGeometry
  ∷ Manifold
  ∷ LieTheory
  ∷ SpinGeometry
  ∷ Number
  ∷ Arithmetic
  ∷ Valuation
  ∷ PrimeDecomposition
  ∷ LocalGlobal
  ∷ Modular
  ∷ Automorphic
  ∷ TransitionSystem
  ∷ RewriteDynamics
  ∷ DynamicalSystem
  ∷ Control
  ∷ Automaton
  ∷ FormalLanguage
  ∷ Operator
  ∷ Functional
  ∷ Hamiltonian
  ∷ Lyapunov
  ∷ GradientFlow
  ∷ Optimization
  ∷ Information
  ∷ Entropy
  ∷ Probability
  ∷ Statistical
  ∷ Inference
  ∷ Estimator
  ∷ HypothesisTest
  ∷ ConfidenceInterval
  ∷ RobustStatistic
  ∷ OutlierDetection
  ∷ Sampling
  ∷ ExperimentalDesign
  ∷ DecisionTheory
  ∷ Bayesian
  ∷ Frequentist
  ∷ CausalInference
  ∷ UncertaintyQuantification
  ∷ ModelSelection
  ∷ InformationCriterion
  ∷ Risk
  ∷ Reliability
  ∷ ExtremeValue
  ∷ TimeSeries
  ∷ StochasticProcess
  ∷ Cryptographic
  ∷ TrapdoorProjection
  ∷ SecretWitness
  ∷ QuotientResidue
  ∷ HiddenLift
  ∷ Commitment
  ∷ Governance
  ∷ SymbolicRational
  ∷ []

canonicalFormalLensKindCount : Nat
canonicalFormalLensKindCount = listCount canonicalFormalLensKinds

canonicalFormalLensFamilies : List FormalLensFamily
canonicalFormalLensFamilies = map familyOf canonicalFormalLensKinds

canonicalFormalLensFamilyCount : Nat
canonicalFormalLensFamilyCount = listCount canonicalFormalLensFamilies

canonicalFormalLensFamiliesAreCanonical :
  canonicalFormalLensFamilies ≡ map familyOf canonicalFormalLensKinds
canonicalFormalLensFamiliesAreCanonical = refl

canonicalFormalLensKindCountIsCanonical :
  canonicalFormalLensKindCount ≡
  listCount canonicalFormalLensKinds
canonicalFormalLensKindCountIsCanonical = refl

------------------------------------------------------------------------
-- Reusable receipt surface.

record FormalLensVocabularyCore : Set where
  constructor mkFormalLensVocabularyCore
  field
    lensKind :
      FormalLensKind

    lensFamily :
      FormalLensFamily

    lensFamilyMatchesCanonical :
      familyOf lensKind ≡ lensFamily

    candidateOnly :
      Bool

    promoted :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedIsFalse :
      promoted ≡ false

open FormalLensVocabularyCore public

------------------------------------------------------------------------
-- Canonical example receipts.

symbolicRationalFormalLensVocabulary :
  FormalLensVocabularyCore
symbolicRationalFormalLensVocabulary =
  mkFormalLensVocabularyCore
    SymbolicRational
    SymbolicRationalFamily
    refl
    true
    false
    refl
    refl

hiddenLiftFormalLensVocabulary :
  FormalLensVocabularyCore
hiddenLiftFormalLensVocabulary =
  mkFormalLensVocabularyCore
    HiddenLift
    CryptographicFamily
    refl
    true
    false
    refl
    refl

statisticalFormalLensVocabulary :
  FormalLensVocabularyCore
statisticalFormalLensVocabulary =
  mkFormalLensVocabularyCore
    Statistical
    StatisticalFamily
    refl
    true
    false
    refl
    refl

gradientFlowFormalLensVocabulary :
  FormalLensVocabularyCore
gradientFlowFormalLensVocabulary =
  mkFormalLensVocabularyCore
    GradientFlow
    Dynamical
    refl
    true
    false
    refl
    refl
