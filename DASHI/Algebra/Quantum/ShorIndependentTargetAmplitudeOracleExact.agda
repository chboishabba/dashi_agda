module DASHI.Algebra.Quantum.ShorIndependentTargetAmplitudeOracleExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
import Data.Nat.Properties as NatP

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Graph
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorScalarAmplitudeCarrierExact as Scalar

------------------------------------------------------------------------
-- INDEPENDENT EXPONENT x TARGET CARRIER
--
-- The Q1 graph carrier is sufficient to prove exact computation:
--
--   |x,clean> <-> |x,f(x)>.
--
-- It is NOT closed under the next Shor operation.  Fourier transformation acts
-- on the exponent coordinate while the function-value register is retained, so
-- a basis term |x,f(x)> contributes terms |k,f(x)> for k != x.  Those terms are
-- generally off the graph y=f(k).
--
-- This owner repairs exactly that representation seam.  Target values are an
-- independent coordinate.  The oracle uses the smallest reversible extension
-- of the Q1 graph involution: clean <-> the exact computed target and every
-- other off-graph target is fixed.  This is a valid permutation extension of
-- the exact clean computation, but it is NOT identified with the conventional
-- dirty-target XOR/addition oracle or with a gate decomposition.
--
-- We then lift that independent-target permutation over the scalar-parametric
-- formal amplitude syntax.  The resulting register can represent exponent
-- relabelling with the target held fixed, which is the basis-level closure QFT
-- requires.  Actual cyclic phase coefficients, normalization, interference,
-- Born measurement and QFT inversion remain separate.
------------------------------------------------------------------------

data IndependentTargetState
    (B : Finite.FiniteBasis)
    (base modulus : Nat)
    (modulusNonZero : B369.NonZero modulus) : Set where
  cleanTarget :
    Finite.Basis B →
    IndependentTargetState B base modulus modulusNonZero
  targetValue :
    Finite.Basis B → Nat →
    IndependentTargetState B base modulus modulusNonZero

independentExponent :
  ∀ {B base modulus modulusNonZero} →
  IndependentTargetState B base modulus modulusNonZero →
  Finite.Basis B
independentExponent (cleanTarget b) = b
independentExponent (targetValue b value) = b

computedTargetState :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.Basis B →
  IndependentTargetState B base modulus modulusNonZero
computedTargetState B base modulus modulusNonZero b =
  targetValue b (Graph.powModAtBasis B base modulus modulusNonZero b)

relabelExponent :
  ∀ {B base modulus modulusNonZero} →
  Finite.Basis B →
  IndependentTargetState B base modulus modulusNonZero →
  IndependentTargetState B base modulus modulusNonZero
relabelExponent newExponent (cleanTarget oldExponent) =
  cleanTarget newExponent
relabelExponent newExponent (targetValue oldExponent value) =
  targetValue newExponent value

relabelExponentRetainsTarget :
  ∀ {B base modulus modulusNonZero}
    (newExponent oldExponent : Finite.Basis B)
    (value : Nat) →
  relabelExponent newExponent
    (targetValue {base = base} {modulus = modulus}
      {modulusNonZero = modulusNonZero} oldExponent value)
  ≡ targetValue newExponent value
relabelExponentRetainsTarget newExponent oldExponent value = refl

independentTargetOracleStep :
  ∀ {B base modulus modulusNonZero} →
  IndependentTargetState B base modulus modulusNonZero →
  IndependentTargetState B base modulus modulusNonZero
independentTargetOracleStep
  {B} {base} {modulus} {modulusNonZero}
  (cleanTarget b) =
  computedTargetState B base modulus modulusNonZero b
independentTargetOracleStep
  {B} {base} {modulus} {modulusNonZero}
  (targetValue b value)
  with NatP._≟_ value
    (Graph.powModAtBasis B base modulus modulusNonZero b)
... | yes equality = cleanTarget b
... | no inequality = targetValue b value

independentTargetOracleStepInvolutive :
  ∀ {B base modulus modulusNonZero} →
  (state : IndependentTargetState B base modulus modulusNonZero) →
  independentTargetOracleStep (independentTargetOracleStep state) ≡ state
independentTargetOracleStepInvolutive
  {B} {base} {modulus} {modulusNonZero}
  (cleanTarget b)
  with NatP._≟_
    (Graph.powModAtBasis B base modulus modulusNonZero b)
    (Graph.powModAtBasis B base modulus modulusNonZero b)
... | yes equality = refl
... | no inequality = ⊥-elim (inequality refl)
independentTargetOracleStepInvolutive
  {B} {base} {modulus} {modulusNonZero}
  (targetValue b value)
  with NatP._≟_ value
    (Graph.powModAtBasis B base modulus modulusNonZero b)
... | yes equality rewrite equality
  with NatP._≟_
    (Graph.powModAtBasis B base modulus modulusNonZero b)
    (Graph.powModAtBasis B base modulus modulusNonZero b)
...   | yes same = refl
...   | no impossible = ⊥-elim (impossible refl)
... | no inequality
  with NatP._≟_ value
    (Graph.powModAtBasis B base modulus modulusNonZero b)
...   | yes equality = ⊥-elim (inequality equality)
...   | no same = refl

graphToIndependent :
  ∀ {B base modulus modulusNonZero} →
  Graph.PowModGraphState B base modulus modulusNonZero →
  IndependentTargetState B base modulus modulusNonZero
graphToIndependent (Graph.clean b) = cleanTarget b
graphToIndependent (Graph.loaded b value exact) = targetValue b value

graphIndependentIntertwining :
  ∀ {B base modulus modulusNonZero} →
  (graphState : Graph.PowModGraphState B base modulus modulusNonZero) →
  independentTargetOracleStep (graphToIndependent graphState)
  ≡ graphToIndependent (Graph.powModGraphStep graphState)
graphIndependentIntertwining
  {B} {base} {modulus} {modulusNonZero}
  (Graph.clean b) = refl
graphIndependentIntertwining
  {B} {base} {modulus} {modulusNonZero}
  (Graph.loaded b value exact)
  rewrite exact
  with NatP._≟_
    (Graph.powModAtBasis B base modulus modulusNonZero b)
    (Graph.powModAtBasis B base modulus modulusNonZero b)
... | yes equality = refl
... | no inequality = ⊥-elim (inequality refl)

------------------------------------------------------------------------
-- Scalar formal amplitudes over the independent-target basis.
------------------------------------------------------------------------

record IndependentTargetAmplitudeState
    (Coefficient : Set)
    (B : Finite.FiniteBasis)
    (base modulus : Nat)
    (modulusNonZero : B369.NonZero modulus) : Set where
  constructor independentTargetAmplitudeState
  field
    classicalTag : Finite.Basis B
    amplitudeExpression :
      Scalar.ScalarAmplitudeExpression Coefficient
        (IndependentTargetState B base modulus modulusNonZero)

open IndependentTargetAmplitudeState public

independentTargetAmplitudeRegister :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.FiniteQuantumRegister B
independentTargetAmplitudeRegister Coefficient B base modulus modulusNonZero = record
  { State = IndependentTargetAmplitudeState
      Coefficient B base modulus modulusNonZero
  ; prepare = λ b → independentTargetAmplitudeState b
      (Scalar.scalarBasis (cleanTarget b))
  ; observe = classicalTag
  ; observePrepared = λ b → refl
  }

embedIndependentBasis :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  IndependentTargetState B base modulus modulusNonZero →
  Finite.State
    (independentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
embedIndependentBasis state =
  independentTargetAmplitudeState
    (independentExponent state)
    (Scalar.scalarBasis state)

embedGraphState :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Graph.PowModGraphState B base modulus modulusNonZero →
  Finite.State
    (independentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
embedGraphState graphState =
  embedIndependentBasis (graphToIndependent graphState)

mapIndependentTargetAmplitude :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Finite.State
    (independentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero) →
  Finite.State
    (independentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
mapIndependentTargetAmplitude
  (independentTargetAmplitudeState tag expression) =
  independentTargetAmplitudeState tag
    (Scalar.mapScalarAmplitudeBasis independentTargetOracleStep expression)

mapIndependentTargetAmplitudeInvolutive :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  (state : Finite.State
    (independentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)) →
  mapIndependentTargetAmplitude (mapIndependentTargetAmplitude state) ≡ state
mapIndependentTargetAmplitudeInvolutive
  (independentTargetAmplitudeState tag expression)
  rewrite Scalar.mapScalarAmplitudeBasisInvolutive
    independentTargetOracleStep
    independentTargetOracleStepInvolutive
    expression = refl

independentTargetAmplitudeOracleCircuit :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.ReversibleCircuit
    (independentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
independentTargetAmplitudeOracleCircuit Coefficient B base modulus modulusNonZero = record
  { run = mapIndependentTargetAmplitude
  ; reversible = record
      { inv = mapIndependentTargetAmplitude
      ; left = mapIndependentTargetAmplitudeInvolutive
      ; right = mapIndependentTargetAmplitudeInvolutive
      }
  }

independentTargetCleanEmbedsAsPrepared :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (b : Finite.Basis B) →
  embedGraphState {Coefficient = Coefficient} (Graph.clean b)
  ≡ Finite.prepare
      (independentTargetAmplitudeRegister
        Coefficient B base modulus modulusNonZero)
      b
independentTargetCleanEmbedsAsPrepared Coefficient B base modulus modulusNonZero b = refl

independentTargetAmplitudeOracleIntertwines :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (graphState : Graph.PowModGraphState B base modulus modulusNonZero) →
  Finite.run
    (independentTargetAmplitudeOracleCircuit
      Coefficient B base modulus modulusNonZero)
    (embedGraphState {Coefficient = Coefficient} graphState)
  ≡ embedGraphState {Coefficient = Coefficient}
      (Graph.powModGraphStep graphState)
independentTargetAmplitudeOracleIntertwines
  Coefficient B base modulus modulusNonZero graphState
  rewrite graphIndependentIntertwining graphState = refl

independentTargetAmplitudeOracleWeld :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero
    (independentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
independentTargetAmplitudeOracleWeld Coefficient B base modulus modulusNonZero = record
  { embedGraphState = embedGraphState
  ; amplitudeOracle =
      independentTargetAmplitudeOracleCircuit
        Coefficient B base modulus modulusNonZero
  ; cleanEmbedsAsPrepared =
      independentTargetCleanEmbedsAsPrepared
        Coefficient B base modulus modulusNonZero
  ; oracleIntertwinesGraph =
      independentTargetAmplitudeOracleIntertwines
        Coefficient B base modulus modulusNonZero
  }

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record IndependentTargetAmplitudeBoundary : Set where
  constructor independentTargetAmplitudeBoundary
  field
    exponentTargetCoordinatesIndependent : Bool
    qftExponentRelabellingCarrierClosed : Bool
    exactCleanPowModComputationPreserved : Bool
    reversibleOffGraphExtensionConstructed : Bool
    amplitudeOracleWeldInhabited : Bool
    conventionalDirtyTargetOracleClaimed : Bool
    finiteTargetEnumerationConstructed : Bool
    complexScalarLawsConstructed : Bool
    cyclicQFTActionConstructed : Bool
    bornMeasurementConstructed : Bool

canonicalIndependentTargetAmplitudeBoundary : IndependentTargetAmplitudeBoundary
canonicalIndependentTargetAmplitudeBoundary =
  independentTargetAmplitudeBoundary
    true true true true true false false false false false
