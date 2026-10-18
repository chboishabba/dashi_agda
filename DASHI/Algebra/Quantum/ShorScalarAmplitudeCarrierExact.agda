module DASHI.Algebra.Quantum.ShorScalarAmplitudeCarrierExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Graph
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix

------------------------------------------------------------------------
-- SCALAR-PARAMETRIC FORMAL AMPLITUDE CARRIER
--
-- `ShorFreeAmplitudePowModOracleExact` established that Q1's exact reversible
-- basis action lifts structurally over finite superposition syntax.  Its
-- weighting labels were Nat-valued, which is too narrow for a genuine cyclic
-- Fourier action: C4 already needs the phases 1,i,-1,-i and normalization.
--
-- This owner performs only the representation-generalization that is forced by
-- that observation.  Coefficients are an arbitrary Set.  We provide formal
-- zero, basis kets, scalar-labelled weighting, and binary addition, and lift
-- the exact Q1 basis involution structurally.  No addition/multiplication laws
-- on coefficients are assumed here and no quotient by module laws is taken.
--
-- Consequently this is a suitable SAME-register landing surface for a later
-- exact scalar/character QFT action, but it is not itself a complex vector
-- space, Hilbert space, normalized state, Born model, or QFT.
------------------------------------------------------------------------

data ScalarAmplitudeExpression
    (Coefficient GraphState : Set) : Set where
  scalarZero : ScalarAmplitudeExpression Coefficient GraphState
  scalarBasis : GraphState → ScalarAmplitudeExpression Coefficient GraphState
  scalarScale :
    Coefficient →
    ScalarAmplitudeExpression Coefficient GraphState →
    ScalarAmplitudeExpression Coefficient GraphState
  scalarAdd :
    ScalarAmplitudeExpression Coefficient GraphState →
    ScalarAmplitudeExpression Coefficient GraphState →
    ScalarAmplitudeExpression Coefficient GraphState

mapScalarAmplitudeBasis :
  ∀ {Coefficient A B : Set} →
  (A → B) →
  ScalarAmplitudeExpression Coefficient A →
  ScalarAmplitudeExpression Coefficient B
mapScalarAmplitudeBasis f scalarZero = scalarZero
mapScalarAmplitudeBasis f (scalarBasis x) = scalarBasis (f x)
mapScalarAmplitudeBasis f (scalarScale coefficient ψ) =
  scalarScale coefficient (mapScalarAmplitudeBasis f ψ)
mapScalarAmplitudeBasis f (scalarAdd ψ φ) =
  scalarAdd
    (mapScalarAmplitudeBasis f ψ)
    (mapScalarAmplitudeBasis f φ)

mapScalarAmplitudeBasisInvolutive :
  ∀ {Coefficient A : Set} →
  (f : A → A) →
  (fInvolutive : ∀ x → f (f x) ≡ x) →
  (ψ : ScalarAmplitudeExpression Coefficient A) →
  mapScalarAmplitudeBasis f (mapScalarAmplitudeBasis f ψ) ≡ ψ
mapScalarAmplitudeBasisInvolutive f involutive scalarZero = refl
mapScalarAmplitudeBasisInvolutive f involutive (scalarBasis x)
  rewrite involutive x = refl
mapScalarAmplitudeBasisInvolutive f involutive (scalarScale coefficient ψ)
  rewrite mapScalarAmplitudeBasisInvolutive f involutive ψ = refl
mapScalarAmplitudeBasisInvolutive f involutive (scalarAdd ψ φ)
  rewrite mapScalarAmplitudeBasisInvolutive f involutive ψ
        | mapScalarAmplitudeBasisInvolutive f involutive φ = refl

record ScalarAmplitudeState
    (Coefficient Basis GraphState : Set) : Set where
  constructor scalarAmplitudeState
  field
    classicalTag : Basis
    scalarExpression : ScalarAmplitudeExpression Coefficient GraphState

open ScalarAmplitudeState public

graphBasis :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Graph.PowModGraphState B base modulus modulusNonZero →
  Finite.Basis B
graphBasis (Graph.clean b) = b
graphBasis (Graph.loaded b value exact) = b

scalarAmplitudeRegister :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.FiniteQuantumRegister B
scalarAmplitudeRegister Coefficient B base modulus modulusNonZero = record
  { State = ScalarAmplitudeState
      Coefficient
      (Finite.Basis B)
      (Graph.PowModGraphState B base modulus modulusNonZero)
  ; prepare = λ b → scalarAmplitudeState b (scalarBasis (Graph.clean b))
  ; observe = classicalTag
  ; observePrepared = λ b → refl
  }

scalarBasisKet :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Graph.PowModGraphState B base modulus modulusNonZero →
  Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)
scalarBasisKet g =
  scalarAmplitudeState (graphBasis g) (scalarBasis g)

scalarWeight :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Coefficient →
  Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero) →
  Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)
scalarWeight coefficient (scalarAmplitudeState tag ψ) =
  scalarAmplitudeState tag (scalarScale coefficient ψ)

scalarSuperpose :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero) →
  Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero) →
  Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)
scalarSuperpose
  (scalarAmplitudeState leftTag left)
  (scalarAmplitudeState rightTag right) =
  scalarAmplitudeState leftTag (scalarAdd left right)

scalarAmplitudeOracleStep :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero) →
  Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)
scalarAmplitudeOracleStep (scalarAmplitudeState tag ψ) =
  scalarAmplitudeState tag
    (mapScalarAmplitudeBasis Graph.powModGraphStep ψ)

scalarAmplitudeOracleStepInvolutive :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  (ψ : Finite.State
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)) →
  scalarAmplitudeOracleStep (scalarAmplitudeOracleStep ψ) ≡ ψ
scalarAmplitudeOracleStepInvolutive (scalarAmplitudeState tag ψ)
  rewrite mapScalarAmplitudeBasisInvolutive
    Graph.powModGraphStep
    Graph.powModGraphStepInvolutive
    ψ = refl

scalarAmplitudeOracleCircuit :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.ReversibleCircuit
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)
scalarAmplitudeOracleCircuit Coefficient B base modulus modulusNonZero = record
  { run = scalarAmplitudeOracleStep
  ; reversible = record
      { inv = scalarAmplitudeOracleStep
      ; left = scalarAmplitudeOracleStepInvolutive
      ; right = scalarAmplitudeOracleStepInvolutive
      }
  }

scalarAmplitudeCleanEmbedsAsPrepared :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (b : Finite.Basis B) →
  scalarBasisKet {Coefficient = Coefficient} (Graph.clean b)
  ≡ Finite.prepare
      (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)
      b
scalarAmplitudeCleanEmbedsAsPrepared Coefficient B base modulus modulusNonZero b = refl

scalarAmplitudeOracleIntertwines :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (g : Graph.PowModGraphState B base modulus modulusNonZero) →
  Finite.run
    (scalarAmplitudeOracleCircuit Coefficient B base modulus modulusNonZero)
    (scalarBasisKet {Coefficient = Coefficient} g)
  ≡ scalarBasisKet {Coefficient = Coefficient} (Graph.powModGraphStep g)
scalarAmplitudeOracleIntertwines Coefficient B base modulus modulusNonZero
  (Graph.clean b) = refl
scalarAmplitudeOracleIntertwines Coefficient B base modulus modulusNonZero
  (Graph.loaded b value exact) = refl

scalarAmplitudeOraclePreservesWeight :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (coefficient : Coefficient) →
  (g : Graph.PowModGraphState B base modulus modulusNonZero) →
  Finite.run
    (scalarAmplitudeOracleCircuit Coefficient B base modulus modulusNonZero)
    (scalarWeight coefficient
      (scalarBasisKet {Coefficient = Coefficient} g))
  ≡ scalarWeight coefficient
      (scalarBasisKet {Coefficient = Coefficient}
        (Graph.powModGraphStep g))
scalarAmplitudeOraclePreservesWeight Coefficient B base modulus modulusNonZero
  coefficient (Graph.clean b) = refl
scalarAmplitudeOraclePreservesWeight Coefficient B base modulus modulusNonZero
  coefficient (Graph.loaded b value exact) = refl

scalarAmplitudeOracleWeld :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero
    (scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)
scalarAmplitudeOracleWeld Coefficient B base modulus modulusNonZero = record
  { embedGraphState = scalarBasisKet
  ; amplitudeOracle =
      scalarAmplitudeOracleCircuit Coefficient B base modulus modulusNonZero
  ; cleanEmbedsAsPrepared =
      scalarAmplitudeCleanEmbedsAsPrepared
        Coefficient B base modulus modulusNonZero
  ; oracleIntertwinesGraph =
      scalarAmplitudeOracleIntertwines
        Coefficient B base modulus modulusNonZero
  }

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record ScalarAmplitudeCarrierBoundary : Set where
  constructor scalarAmplitudeCarrierBoundary
  field
    arbitraryScalarLabelsSupported : Bool
    exactQ1BasisInvolutionLifted : Bool
    amplitudeOracleWeldInhabited : Bool
    coefficientRingLawsAssumed : Bool
    moduleQuotientConstructed : Bool
    complexPhaseActionConstructed : Bool
    cyclicQFTConstructed : Bool
    normalizationConstructed : Bool
    bornMeasurementConstructed : Bool

canonicalScalarAmplitudeCarrierBoundary : ScalarAmplitudeCarrierBoundary
canonicalScalarAmplitudeCarrierBoundary =
  scalarAmplitudeCarrierBoundary
    true true true false false false false false false
