module DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import Data.Vec.Base as Vec
open import Data.List.Base using (List; []; _∷_; allFin)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Quantum
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Graph
import DASHI.Algebra.Quantum.ShorFinitePowModTargetExact as PowTarget
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorCyclicExponentBasisExact as Cyclic
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase

------------------------------------------------------------------------
-- CANONICAL FINITE VECTOR AMPLITUDE REGISTER
--
--   Vec (Vec Coefficient (N + 1)) Q
--
-- Rows are exponent coordinates Fin Q.  Column zero is the distinguished clean
-- target; column suc(y) is residue y : Fin N.  Ordinary propositional equality
-- is structural Vec equality: no extensionality axiom and no quotient by
-- module syntax is required.
--
-- The exact RSA.powMod oracle is a coordinate permutation in each exponent row:
-- clean <-> suc(powMod x), all other target coordinates fixed.  The literal
-- cyclic QFT is a finite character sum along the exponent dimension while every
-- target column is retained.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Local constructive Vec tabulation/extensionality.
------------------------------------------------------------------------

tabulateVec :
  ∀ {A : Set} {n : Nat} →
  (Fin.Fin n → A) → Vec.Vec A n
tabulateVec {n = 0} f = Vec.[]
tabulateVec {n = suc n} f =
  f Fin.zero Vec.∷ tabulateVec (λ i → f (Fin.suc i))

lookupTabulateVec :
  ∀ {A : Set} {n : Nat}
    (f : Fin.Fin n → A)
    (i : Fin.Fin n) →
  Vec.lookup (tabulateVec f) i ≡ f i
lookupTabulateVec {n = suc n} f Fin.zero = refl
lookupTabulateVec {n = suc n} f (Fin.suc i) =
  lookupTabulateVec (λ j → f (Fin.suc j)) i

vecExtensionality :
  ∀ {A : Set} {n : Nat}
    (xs ys : Vec.Vec A n) →
  (∀ i → Vec.lookup xs i ≡ Vec.lookup ys i) →
  xs ≡ ys
vecExtensionality Vec.[] Vec.[] pointwise = refl
vecExtensionality (x Vec.∷ xs) (y Vec.∷ ys) pointwise
  rewrite pointwise Fin.zero
        | vecExtensionality xs ys (λ i → pointwise (Fin.suc i)) = refl

------------------------------------------------------------------------
-- Finite target permutation induced by exact RSA.powMod.
------------------------------------------------------------------------

computedResidue :
  ∀ {Q N}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat) →
  Fin.Fin Q → Fin.Fin N
computedResidue {Q} {N} qNonZero nNonZero base x =
  PowTarget.powModFiniteTarget
    base
    (Quantum.encode (Cyclic.cyclicExponentBasis Q qNonZero) x)
    N
    nNonZero

computedTargetIndex :
  ∀ {Q N}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat) →
  Fin.Fin Q → Fin.Fin (suc N)
computedTargetIndex qNonZero nNonZero base x =
  Fin.suc (computedResidue qNonZero nNonZero base x)

oracleTargetIndex :
  ∀ {Q N}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat) →
  Fin.Fin Q → Fin.Fin (suc N) → Fin.Fin (suc N)
oracleTargetIndex qNonZero nNonZero base x Fin.zero =
  computedTargetIndex qNonZero nNonZero base x
oracleTargetIndex qNonZero nNonZero base x (Fin.suc y)
  with FinP._≟_ y (computedResidue qNonZero nNonZero base x)
... | yes equality = Fin.zero
... | no inequality = Fin.suc y

oracleTargetIndexInvolutive :
  ∀ {Q N}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (x : Fin.Fin Q)
    (target : Fin.Fin (suc N)) →
  oracleTargetIndex qNonZero nNonZero base x
    (oracleTargetIndex qNonZero nNonZero base x target)
  ≡ target
oracleTargetIndexInvolutive qNonZero nNonZero base x Fin.zero
  with FinP._≟_
    (computedResidue qNonZero nNonZero base x)
    (computedResidue qNonZero nNonZero base x)
... | yes equality = refl
... | no inequality = ⊥-elim (inequality refl)
oracleTargetIndexInvolutive qNonZero nNonZero base x (Fin.suc y)
  with FinP._≟_ y (computedResidue qNonZero nNonZero base x)
... | yes equality rewrite equality = refl
... | no inequality
  with FinP._≟_ y (computedResidue qNonZero nNonZero base x)
...   | yes equality = ⊥-elim (inequality equality)
...   | no same = refl

------------------------------------------------------------------------
-- Canonical amplitude table and basis states.
------------------------------------------------------------------------

AmplitudeTable : Set → Nat → Nat → Set
AmplitudeTable Coefficient Q N =
  Vec.Vec (Vec.Vec Coefficient (suc N)) Q

tableLookup :
  ∀ {Coefficient Q N} →
  AmplitudeTable Coefficient Q N →
  Fin.Fin Q → Fin.Fin (suc N) → Coefficient
tableLookup table x target =
  Vec.lookup (Vec.lookup table x) target

tabulateTable :
  ∀ {Coefficient Q N} →
  (Fin.Fin Q → Fin.Fin (suc N) → Coefficient) →
  AmplitudeTable Coefficient Q N
tabulateTable f =
  tabulateVec (λ x → tabulateVec (f x))

lookupTabulateTable :
  ∀ {Coefficient Q N}
    (f : Fin.Fin Q → Fin.Fin (suc N) → Coefficient)
    (x : Fin.Fin Q)
    (target : Fin.Fin (suc N)) →
  tableLookup (tabulateTable f) x target ≡ f x target
lookupTabulateTable f x target
  rewrite lookupTabulateVec (λ row → tabulateVec (f row)) x
        | lookupTabulateVec (f x) target = refl

tableExtensionality :
  ∀ {Coefficient Q N}
    (left right : AmplitudeTable Coefficient Q N) →
  (∀ x target → tableLookup left x target ≡ tableLookup right x target) →
  left ≡ right
tableExtensionality left right pointwise =
  vecExtensionality left right λ x →
    vecExtensionality (Vec.lookup left x) (Vec.lookup right x)
      (pointwise x)

basisTable :
  ∀ {Coefficient Q N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Fin.Fin Q → Fin.Fin (suc N) →
  AmplitudeTable Coefficient Q N
basisTable A exponent target =
  tabulateTable λ x slot → decide x slot
  where
    decide : Fin.Fin Q → Fin.Fin (suc N) → Coefficient
    decide x slot with FinP._≟_ exponent x | FinP._≟_ target slot
    ... | yes refl | yes refl = Phase.oneCoefficient A
    ... | _ | _ = Phase.zeroCoefficient A

record VectorAmplitudeState
    {Coefficient : Set}
    (Q N : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) : Set where
  constructor vectorAmplitudeState
  field
    classicalTag : Fin.Fin Q
    amplitudeTable : AmplitudeTable Coefficient Q N

open VectorAmplitudeState public

FiniteVectorAmplitudeState :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) → Set
FiniteVectorAmplitudeState {Q} {N} qNonZero nNonZero base A =
  VectorAmplitudeState Q N A

vectorAmplitudeRegister :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Quantum.FiniteQuantumRegister
    (Cyclic.cyclicExponentBasis Q qNonZero)
vectorAmplitudeRegister {Q} {N} qNonZero nNonZero base A = record
  { State = VectorAmplitudeState Q N A
  ; prepare = λ x → vectorAmplitudeState x (basisTable A x Fin.zero)
  ; observe = classicalTag
  ; observePrepared = λ x → refl
  }

------------------------------------------------------------------------
-- Exact powMod permutation on the canonical amplitude table.
------------------------------------------------------------------------

vectorOracleTable :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  AmplitudeTable Coefficient Q N →
  AmplitudeTable Coefficient Q N
vectorOracleTable qNonZero nNonZero base A table =
  tabulateTable λ x target →
    tableLookup table x
      (oracleTargetIndex qNonZero nNonZero base x target)

vectorOracleTableLookup :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (table : AmplitudeTable Coefficient Q N)
    (x : Fin.Fin Q)
    (target : Fin.Fin (suc N)) →
  tableLookup (vectorOracleTable qNonZero nNonZero base A table) x target
  ≡ tableLookup table x
      (oracleTargetIndex qNonZero nNonZero base x target)
vectorOracleTableLookup qNonZero nNonZero base A table x target =
  lookupTabulateTable
    (λ row slot → tableLookup table row
      (oracleTargetIndex qNonZero nNonZero base row slot))
    x target

vectorOracleTableInvolutive :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (table : AmplitudeTable Coefficient Q N) →
  vectorOracleTable qNonZero nNonZero base A
    (vectorOracleTable qNonZero nNonZero base A table)
  ≡ table
vectorOracleTableInvolutive qNonZero nNonZero base A table =
  tableExtensionality _ _ λ x target →
    trans
      (vectorOracleTableLookup qNonZero nNonZero base A
        (vectorOracleTable qNonZero nNonZero base A table) x target)
      (trans
        (vectorOracleTableLookup qNonZero nNonZero base A table x
          (oracleTargetIndex qNonZero nNonZero base x target))
        (cong (tableLookup table x)
          (oracleTargetIndexInvolutive qNonZero nNonZero base x target)))

vectorOracleState :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  VectorAmplitudeState Q N A →
  VectorAmplitudeState Q N A
vectorOracleState qNonZero nNonZero base A
  (vectorAmplitudeState tag table) =
  vectorAmplitudeState tag
    (vectorOracleTable qNonZero nNonZero base A table)

vectorOracleStateInvolutive :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (ψ : VectorAmplitudeState Q N A) →
  vectorOracleState qNonZero nNonZero base A
    (vectorOracleState qNonZero nNonZero base A ψ)
  ≡ ψ
vectorOracleStateInvolutive qNonZero nNonZero base A
  (vectorAmplitudeState tag table)
  rewrite vectorOracleTableInvolutive qNonZero nNonZero base A table = refl

vectorOracleCircuit :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Quantum.ReversibleCircuit
    (vectorAmplitudeRegister qNonZero nNonZero base A)
vectorOracleCircuit qNonZero nNonZero base A = record
  { run = vectorOracleState qNonZero nNonZero base A
  ; reversible = record
      { inv = vectorOracleState qNonZero nNonZero base A
      ; left = vectorOracleStateInvolutive qNonZero nNonZero base A
      ; right = vectorOracleStateInvolutive qNonZero nNonZero base A
      }
  }

------------------------------------------------------------------------
-- Q1 graph embedding and exact oracle intertwining.
------------------------------------------------------------------------

embedGraphState :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Graph.PowModGraphState
    (Cyclic.cyclicExponentBasis Q qNonZero)
    base N nNonZero →
  Quantum.State (vectorAmplitudeRegister qNonZero nNonZero base A)
embedGraphState qNonZero nNonZero base A (Graph.clean x) =
  Quantum.prepare (vectorAmplitudeRegister qNonZero nNonZero base A) x
embedGraphState qNonZero nNonZero base A (Graph.loaded x value exact) =
  vectorOracleState qNonZero nNonZero base A
    (Quantum.prepare (vectorAmplitudeRegister qNonZero nNonZero base A) x)

vectorOracleIntertwinesGraph :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (graphState : Graph.PowModGraphState
    (Cyclic.cyclicExponentBasis Q qNonZero)
    base N nNonZero) →
  Quantum.run (vectorOracleCircuit qNonZero nNonZero base A)
    (embedGraphState qNonZero nNonZero base A graphState)
  ≡ embedGraphState qNonZero nNonZero base A
      (Graph.powModGraphStep graphState)
vectorOracleIntertwinesGraph qNonZero nNonZero base A (Graph.clean x) = refl
vectorOracleIntertwinesGraph qNonZero nNonZero base A
  (Graph.loaded x value exact) =
  vectorOracleStateInvolutive qNonZero nNonZero base A
    (Quantum.prepare (vectorAmplitudeRegister qNonZero nNonZero base A) x)

vectorAmplitudeOracleWeld :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Prefix.ShorAmplitudeOracleWeld
    (Cyclic.cyclicExponentBasis Q qNonZero)
    base N nNonZero
    (vectorAmplitudeRegister qNonZero nNonZero base A)
vectorAmplitudeOracleWeld qNonZero nNonZero base A = record
  { embedGraphState = embedGraphState qNonZero nNonZero base A
  ; amplitudeOracle = vectorOracleCircuit qNonZero nNonZero base A
  ; cleanEmbedsAsPrepared = λ x → refl
  ; oracleIntertwinesGraph =
      vectorOracleIntertwinesGraph qNonZero nNonZero base A
  }

------------------------------------------------------------------------
-- Literal cyclic character transform on the SAME canonical table.
------------------------------------------------------------------------

sumCoefficients :
  ∀ {Coefficient Q}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (Fin.Fin Q → Coefficient) →
  List (Fin.Fin Q) → Coefficient
sumCoefficients A term [] = Phase.zeroCoefficient A
sumCoefficients A term (x ∷ xs) =
  Phase.addCoefficient A (term x) (sumCoefficients A term xs)

vectorForwardTable :
  ∀ {Q N Coefficient}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  AmplitudeTable Coefficient Q N →
  AmplitudeTable Coefficient Q N
vectorForwardTable {Q} A table =
  tabulateTable λ k target →
    sumCoefficients A
      (λ x →
        Phase.multiplyCoefficient A
          (Phase.normalisation A)
          (Phase.multiplyCoefficient A
            (Phase.phase A k x)
            (tableLookup table x target)))
      (allFin Q)

vectorInverseTable :
  ∀ {Q N Coefficient}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  AmplitudeTable Coefficient Q N →
  AmplitudeTable Coefficient Q N
vectorInverseTable {Q} A table =
  tabulateTable λ x target →
    sumCoefficients A
      (λ k →
        Phase.multiplyCoefficient A
          (Phase.normalisation A)
          (Phase.multiplyCoefficient A
            (Phase.inversePhase A x k)
            (tableLookup table k target)))
      (allFin Q)

vectorForwardState :
  ∀ {Q N Coefficient}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  VectorAmplitudeState Q N A →
  VectorAmplitudeState Q N A
vectorForwardState A (vectorAmplitudeState tag table) =
  vectorAmplitudeState tag (vectorForwardTable A table)

vectorInverseState :
  ∀ {Q N Coefficient}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  VectorAmplitudeState Q N A →
  VectorAmplitudeState Q N A
vectorInverseState A (vectorAmplitudeState tag table) =
  vectorAmplitudeState tag (vectorInverseTable A table)

record VectorCyclicPhaseInversionAuthority
    {Q Coefficient}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) : Set₁ where
  constructor vectorCyclicPhaseInversionAuthority
  field
    inverseAfterForwardTable :
      ∀ {N} table →
      vectorInverseTable A (vectorForwardTable A table) ≡ table

    forwardAfterInverseTable :
      ∀ {N} table →
      vectorForwardTable A (vectorInverseTable A table) ≡ table

open VectorCyclicPhaseInversionAuthority public

vectorFiniteFourierTransform :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  VectorCyclicPhaseInversionAuthority A →
  QFT.FiniteFourierTransform
    (vectorAmplitudeRegister qNonZero nNonZero base A)
vectorFiniteFourierTransform qNonZero nNonZero base A I = record
  { fourier = vectorForwardState A
  ; inverseFourier = vectorInverseState A
  ; inverseAfterFourier = inverseAfter
  ; fourierAfterInverse = forwardAfter
  }
  where
    inverseAfter : ∀ ψ → vectorInverseState A (vectorForwardState A ψ) ≡ ψ
    inverseAfter (vectorAmplitudeState tag table)
      rewrite inverseAfterForwardTable I table = refl

    forwardAfter : ∀ ψ → vectorForwardState A (vectorInverseState A ψ) ≡ ψ
    forwardAfter (vectorAmplitudeState tag table)
      rewrite forwardAfterInverseTable I table = refl

record ShorFiniteVectorAmplitudeBoundary : Set where
  constructor shorFiniteVectorAmplitudeBoundary
  field
    canonicalNestedVecCarrier : Bool
    exponentDimensionFinite : Bool
    targetDimensionFiniteWithCleanSlot : Bool
    exactPowModOraclePermutationConstructed : Bool
    oracleReversibilityConstructive : Bool
    q1GraphIntertwiningConstructed : Bool
    literalCyclicCharacterTransformConstructed : Bool
    extensionalityAxiomUsed : Bool
    coefficientFourierInversionStillRequired : Bool
    bornMeasurementStillRequired : Bool

canonicalShorFiniteVectorAmplitudeBoundary : ShorFiniteVectorAmplitudeBoundary
canonicalShorFiniteVectorAmplitudeBoundary =
  shorFiniteVectorAmplitudeBoundary
    true true true true true true true false true true