module DASHI.Algebra.Quantum.ShorFiniteIndependentTargetAmplitudeOracleExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Graph
import DASHI.Algebra.Quantum.ShorFinitePowModTargetExact as Target
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorScalarAmplitudeCarrierExact as Scalar

------------------------------------------------------------------------
-- FINITE INDEPENDENT EXPONENT x TARGET AMPLITUDE CARRIER
--
-- The earlier independent-target owner correctly separated the exponent and
-- target coordinates but left the target as Nat.  RSA.powMod is a remainder,
-- so ShorFinitePowModTargetExact now proves its value lies in Fin modulus.
-- This owner uses that finite residue directly.
--
-- QFT may relabel the exponent while retaining any target residue.  Therefore
-- the basis is closed under the required exponent-only Fourier action, unlike
-- the original exact-graph basis.  The oracle remains the smallest reversible
-- clean <-> exact-computed-target extension; all other target residues are
-- fixed.  No conventional dirty-target addition/XOR oracle is claimed.
------------------------------------------------------------------------

data FiniteIndependentTargetState
    (B : Finite.FiniteBasis)
    (base modulus : Nat)
    (modulusNonZero : B369.NonZero modulus) : Set where
  cleanTarget :
    Finite.Basis B →
    FiniteIndependentTargetState B base modulus modulusNonZero
  targetResidue :
    Finite.Basis B → Fin modulus →
    FiniteIndependentTargetState B base modulus modulusNonZero

finiteIndependentExponent :
  ∀ {B base modulus modulusNonZero} →
  FiniteIndependentTargetState B base modulus modulusNonZero →
  Finite.Basis B
finiteIndependentExponent (cleanTarget b) = b
finiteIndependentExponent (targetResidue b value) = b

computedTargetResidue :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.Basis B → Fin modulus
computedTargetResidue B base modulus modulusNonZero b =
  Target.powModFiniteTarget
    base
    (Finite.encode B b)
    modulus
    modulusNonZero

computedTargetState :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.Basis B →
  FiniteIndependentTargetState B base modulus modulusNonZero
computedTargetState B base modulus modulusNonZero b =
  targetResidue b
    (computedTargetResidue B base modulus modulusNonZero b)

relabelFiniteExponent :
  ∀ {B base modulus modulusNonZero} →
  Finite.Basis B →
  FiniteIndependentTargetState B base modulus modulusNonZero →
  FiniteIndependentTargetState B base modulus modulusNonZero
relabelFiniteExponent newExponent (cleanTarget oldExponent) =
  cleanTarget newExponent
relabelFiniteExponent newExponent (targetResidue oldExponent value) =
  targetResidue newExponent value

finiteIndependentTargetOracleStep :
  ∀ {B base modulus modulusNonZero} →
  FiniteIndependentTargetState B base modulus modulusNonZero →
  FiniteIndependentTargetState B base modulus modulusNonZero
finiteIndependentTargetOracleStep
  {B} {base} {modulus} {modulusNonZero}
  (cleanTarget b) =
  computedTargetState B base modulus modulusNonZero b
finiteIndependentTargetOracleStep
  {B} {base} {modulus} {modulusNonZero}
  (targetResidue b value)
  with FinP._≟_ value
    (computedTargetResidue B base modulus modulusNonZero b)
... | yes equality = cleanTarget b
... | no inequality = targetResidue b value

finiteIndependentTargetOracleStepInvolutive :
  ∀ {B base modulus modulusNonZero} →
  (state : FiniteIndependentTargetState B base modulus modulusNonZero) →
  finiteIndependentTargetOracleStep
    (finiteIndependentTargetOracleStep state) ≡ state
finiteIndependentTargetOracleStepInvolutive
  {B} {base} {modulus} {modulusNonZero}
  (cleanTarget b)
  with FinP._≟_
    (computedTargetResidue B base modulus modulusNonZero b)
    (computedTargetResidue B base modulus modulusNonZero b)
... | yes equality = refl
... | no inequality = ⊥-elim (inequality refl)
finiteIndependentTargetOracleStepInvolutive
  {B} {base} {modulus} {modulusNonZero}
  (targetResidue b value)
  with FinP._≟_ value
    (computedTargetResidue B base modulus modulusNonZero b)
... | yes equality rewrite equality
  with FinP._≟_
    (computedTargetResidue B base modulus modulusNonZero b)
    (computedTargetResidue B base modulus modulusNonZero b)
...   | yes same = refl
...   | no impossible = ⊥-elim (impossible refl)
... | no inequality
  with FinP._≟_ value
    (computedTargetResidue B base modulus modulusNonZero b)
...   | yes equality = ⊥-elim (inequality equality)
...   | no same = refl

graphToFiniteIndependent :
  ∀ {B base modulus modulusNonZero} →
  Graph.PowModGraphState B base modulus modulusNonZero →
  FiniteIndependentTargetState B base modulus modulusNonZero
graphToFiniteIndependent
  {B} {base} {modulus} {modulusNonZero}
  (Graph.clean b) = cleanTarget b
graphToFiniteIndependent
  {B} {base} {modulus} {modulusNonZero}
  (Graph.loaded b value exact) =
  computedTargetState B base modulus modulusNonZero b

graphFiniteIndependentIntertwining :
  ∀ {B base modulus modulusNonZero} →
  (graphState : Graph.PowModGraphState B base modulus modulusNonZero) →
  finiteIndependentTargetOracleStep
    (graphToFiniteIndependent graphState)
  ≡ graphToFiniteIndependent (Graph.powModGraphStep graphState)
graphFiniteIndependentIntertwining
  {B} {base} {modulus} {modulusNonZero}
  (Graph.clean b) = refl
graphFiniteIndependentIntertwining
  {B} {base} {modulus} {modulusNonZero}
  (Graph.loaded b value exact)
  with FinP._≟_
    (computedTargetResidue B base modulus modulusNonZero b)
    (computedTargetResidue B base modulus modulusNonZero b)
... | yes equality = refl
... | no inequality = ⊥-elim (inequality refl)

------------------------------------------------------------------------
-- Scalar-parametric formal amplitudes over the finite product basis.
------------------------------------------------------------------------

record FiniteIndependentTargetAmplitudeState
    (Coefficient : Set)
    (B : Finite.FiniteBasis)
    (base modulus : Nat)
    (modulusNonZero : B369.NonZero modulus) : Set where
  constructor finiteIndependentTargetAmplitudeState
  field
    classicalTag : Finite.Basis B
    amplitudeExpression :
      Scalar.ScalarAmplitudeExpression Coefficient
        (FiniteIndependentTargetState B base modulus modulusNonZero)

open FiniteIndependentTargetAmplitudeState public

finiteIndependentTargetAmplitudeRegister :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.FiniteQuantumRegister B
finiteIndependentTargetAmplitudeRegister Coefficient B base modulus modulusNonZero = record
  { State = FiniteIndependentTargetAmplitudeState
      Coefficient B base modulus modulusNonZero
  ; prepare = λ b → finiteIndependentTargetAmplitudeState b
      (Scalar.scalarBasis (cleanTarget b))
  ; observe = classicalTag
  ; observePrepared = λ b → refl
  }

embedFiniteIndependentBasis :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  FiniteIndependentTargetState B base modulus modulusNonZero →
  Finite.State
    (finiteIndependentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
embedFiniteIndependentBasis state =
  finiteIndependentTargetAmplitudeState
    (finiteIndependentExponent state)
    (Scalar.scalarBasis state)

embedGraphState :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Graph.PowModGraphState B base modulus modulusNonZero →
  Finite.State
    (finiteIndependentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
embedGraphState graphState =
  embedFiniteIndependentBasis (graphToFiniteIndependent graphState)

mapFiniteIndependentTargetAmplitude :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  Finite.State
    (finiteIndependentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero) →
  Finite.State
    (finiteIndependentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
mapFiniteIndependentTargetAmplitude
  (finiteIndependentTargetAmplitudeState tag expression) =
  finiteIndependentTargetAmplitudeState tag
    (Scalar.mapScalarAmplitudeBasis
      finiteIndependentTargetOracleStep expression)

mapFiniteIndependentTargetAmplitudeInvolutive :
  ∀ {Coefficient : Set}
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus} →
  (state : Finite.State
    (finiteIndependentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)) →
  mapFiniteIndependentTargetAmplitude
    (mapFiniteIndependentTargetAmplitude state) ≡ state
mapFiniteIndependentTargetAmplitudeInvolutive
  (finiteIndependentTargetAmplitudeState tag expression)
  rewrite Scalar.mapScalarAmplitudeBasisInvolutive
    finiteIndependentTargetOracleStep
    finiteIndependentTargetOracleStepInvolutive
    expression = refl

finiteIndependentTargetAmplitudeOracleCircuit :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.ReversibleCircuit
    (finiteIndependentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
finiteIndependentTargetAmplitudeOracleCircuit Coefficient B base modulus modulusNonZero = record
  { run = mapFiniteIndependentTargetAmplitude
  ; reversible = record
      { inv = mapFiniteIndependentTargetAmplitude
      ; left = mapFiniteIndependentTargetAmplitudeInvolutive
      ; right = mapFiniteIndependentTargetAmplitudeInvolutive
      }
  }

finiteIndependentTargetAmplitudeOracleIntertwines :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (graphState : Graph.PowModGraphState B base modulus modulusNonZero) →
  Finite.run
    (finiteIndependentTargetAmplitudeOracleCircuit
      Coefficient B base modulus modulusNonZero)
    (embedGraphState {Coefficient = Coefficient} graphState)
  ≡ embedGraphState {Coefficient = Coefficient}
      (Graph.powModGraphStep graphState)
finiteIndependentTargetAmplitudeOracleIntertwines
  Coefficient B base modulus modulusNonZero graphState
  rewrite graphFiniteIndependentIntertwining graphState = refl

finiteIndependentTargetAmplitudeOracleWeld :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero
    (finiteIndependentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
finiteIndependentTargetAmplitudeOracleWeld Coefficient B base modulus modulusNonZero = record
  { embedGraphState = embedGraphState
  ; amplitudeOracle =
      finiteIndependentTargetAmplitudeOracleCircuit
        Coefficient B base modulus modulusNonZero
  ; cleanEmbedsAsPrepared = λ b → refl
  ; oracleIntertwinesGraph =
      finiteIndependentTargetAmplitudeOracleIntertwines
        Coefficient B base modulus modulusNonZero
  }

record FiniteIndependentTargetAmplitudeBoundary : Set where
  constructor finiteIndependentTargetAmplitudeBoundary
  field
    exponentTargetCoordinatesIndependent : Bool
    targetCoordinateIsFinModulus : Bool
    exactRSApowModValueRetained : Bool
    qftExponentRelabellingCarrierClosed : Bool
    amplitudeOracleWeldInhabited : Bool
    conventionalDirtyTargetOracleClaimed : Bool
    cyclicPhaseActionConstructed : Bool
    normalizedQFTConstructed : Bool
    bornMeasurementConstructed : Bool

canonicalFiniteIndependentTargetAmplitudeBoundary :
  FiniteIndependentTargetAmplitudeBoundary
canonicalFiniteIndependentTargetAmplitudeBoundary =
  finiteIndependentTargetAmplitudeBoundary
    true true true true true false false false false
