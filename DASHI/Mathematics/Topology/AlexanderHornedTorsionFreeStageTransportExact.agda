module DASHI.Mathematics.Topology.AlexanderHornedTorsionFreeStageTransportExact where

------------------------------------------------------------------------
-- HATCHER TORSION-FREE TRANSFER: PROOF-BEARING COLIMIT CUT
--
-- Hatcher, Algebraic Topology, Example 2B.2, printed pp.171--172,
-- directly proves (1) stage exteriors have free fundamental groups
-- F_(2^n); (2) inclusion maps are injective; and (3) pi1 of the
-- Alexander horned-ball exterior is their ascending union.
-- Classical free groups are torsion-free.
--
-- NEW THEOREM HERE:
-- Any power-preserving *injective* stage embeddings into a target,
-- whose images cover that target, transfer stage torsion-freeness
-- to the target. A finite quotient cannot pull back a nonidentity
-- finite-order element to a finite-order element in that target.
--
-- This is proof-bearing *conditional transport*, NOT a hidden
-- assertion of the geometry for the 3-copy equivariant construction.
-- The stage injection, stage free-group theorem, and geometric
-- van Kampen equivalence must be INSTANCES. No postulated axioms,
-- no reinterpretation of geometric twist as group torsion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record CoveredInjectivePowerStages : Set₁ where
  field
    Target : Set
    targetIdentity : Target
    targetPower : Nat → Target → Target

    Stage : Nat → Set
    stageIdentity : (n : Nat) → Stage n
    stagePower : (n k : Nat) → Stage n → Stage n

    include : (n : Nat) → Stage n → Target
    inclusionInjective :
      (n : Nat) → {a b : Stage n} →
      include n a ≡ include n b → a ≡ b

    inclusionPreservesIdentity :
      (n : Nat) → include n (stageIdentity n) ≡ targetIdentity

    inclusionPreservesPower :
      (n k : Nat) → (a : Stage n) →
      include n (stagePower n k a) ≡ targetPower k (include n a)

    everyTargetHasFiniteStage :
      (x : Target) →
      Σ Nat (λ n → Σ (Stage n) (λ a → include n a ≡ x))

    finiteStageIsTorsionFree :
      (n k : Nat) → (a : Stage n) →
      stagePower n (suc k) a ≡ stageIdentity n →
      a ≡ stageIdentity n

open CoveredInjectivePowerStages public

-- Nontrivial, noncircular proof: the target's torsion-free law
-- does NOT appear as a field. It follows from the free-stage
-- torsion-free law, coverage, injectivity and power preservation.
targetIsTorsionFree :
  (T : CoveredInjectivePowerStages) →
  (k : Nat) → (x : Target T) →
  targetPower T (suc k) x ≡ targetIdentity T →
  x ≡ targetIdentity T
targetIsTorsionFree T k x powerIsIdentity
  with everyTargetHasFiniteStage T x
... | n , (a , stageRepresentsX) =
  let stagePowerIsIdentity =
        inclusionInjective T n
          (trans
            (inclusionPreservesPower T n (suc k) a)
            (trans
              (cong (targetPower T (suc k)) stageRepresentsX)
              (trans powerIsIdentity
                (sym (inclusionPreservesIdentity T n))))
      stageElementIsIdentity =
        finiteStageIsTorsionFree T n k a stagePowerIsIdentity
  in trans
       (sym stageRepresentsX)
       (trans (cong (include T n) stageElementIsIdentity)
              (inclusionPreservesIdentity T n))

-- Finite-order quotient images are NOT lifts of finite-order source
-- elements: a source element with x^3=1 would be the identity,
-- contradicting its given nonidentity C3 image.
record NontrivialC3QuotientImage
    (T : CoveredInjectivePowerStages) : Set where
  field
    quotient : Target T → C3.C3
    mapsIdentityToZero : quotient (targetIdentity T) ≡ C3.c0
    chosenPreimage : Target T
    imageNontrivial : quotient chosenPreimage ≢ C3.c0

open NontrivialC3QuotientImage public

nonidentityC3ImageCannotHaveOrderThreeInSource :
  (T : CoveredInjectivePowerStages) →
  (Q : NontrivialC3QuotientImage T) →
  targetPower T 3 (chosenPreimage Q) ≡ targetIdentity T →
  ⊥
nonidentityC3ImageCannotHaveOrderThreeInSource T Q cubeIdentity =
  imageNontrivial Q
    (trans
      (cong (quotient Q) (targetIsTorsionFree T 2
        (chosenPreimage Q) cubeIdentity))
      (mapsIdentityToZero Q))

-- Careful: this does NOT deny that an order-three ambient
-- rotation exists in the external semidirect C3 factor. It denies
-- only finite order within the torsion-free source group G.
