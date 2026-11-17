module DASHI.Mathematics.Topology.AlexanderHornedPadicCongruenceNoGoExact where

------------------------------------------------------------------------
-- SOURCE OWNERS:
--  AlexanderHornedProPSolvableBlindExact: recursive commutator
--     meridians map trivially to ANY finite-derived-length target.
--  Classical congruence theorem:
--     ker(GL_n(Zp) -> GL_n(Fp)) is pro-p,
--     hence reduction kernels modulo p^k are finite p groups.
--
-- The old no-go gives a stronger NEW matrix-congruence
-- discriminator: if the finite-level reductions of an ACTUAL
-- integral matrix representation all land in solvable groups,
-- and reductions separate matrices, the representation kills
-- every horn meridian.
--
-- This applies to GL2(Z2) and GL2(Z3) because GL2(F2)
-- and GL2(F3) are solvable. The finite derived series are
-- computed literally in the companion Python audit.
--
-- It does NOT apply to arbitrary GL_n(Qp), nor to GL60(Zp)
-- regular permutation actions with NONSOLVABLE A5 residue.
--
-- This is a conditional theorem about a genuine matrix
-- congruence system; finite GL2/group instances and p-adic
-- separation remain specifically typed supplier obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn
import DASHI.Mathematics.Topology.AlexanderHornedProPSolvableBlindExact as Solv

record SeparatedIntegralCongruenceActor : Set₂ where
  field
    Matrix : Set
    identityMatrix : Matrix
    meridianMatrix : Horn.HornAddress → Matrix

    FiniteReduction : Nat → Solv.SolvableCommutatorTarget
    reduce : (k : Nat) → Matrix →
      Solv.Carrier (FiniteReduction k)

    reductionOfIdentity : ∀ k →
      reduce k identityMatrix
        ≡ Solv.identity (FiniteReduction k)

    reductionRespectsHornCommute : ∀ k address →
      reduce k (meridianMatrix address)
        ≡ Solv.commutator (FiniteReduction k)
            (reduce k (meridianMatrix (Horn.leftChild address)))
            (reduce k (meridianMatrix (Horn.rightChild address)))

    finiteReductionsSeparateMatrices :
      ∀ x → (∀ k →
        reduce k x ≡ reduce k identityMatrix) →
        x ≡ identityMatrix

open SeparatedIntegralCongruenceActor public

finiteLevelHornActor :
  (A : SeparatedIntegralCongruenceActor) →
  (k : Nat) → Solv.HornMeridianRepresentation (FiniteReduction A k)
finiteLevelHornActor A k = record
  { image = reduce A k ∘ meridianMatrix A
  ; respectsRecursiveCommutator = reductionRespectsHornCommute A k
  }
  where
    _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
    (f ∘ g) a = f (g a)

eachFiniteCongruenceKillsMeridian :
  (A : SeparatedIntegralCongruenceActor) →
  ∀ k address →
  reduce A k (meridianMatrix A address)
    ≡ reduce A k (identityMatrix A)
eachFiniteCongruenceKillsMeridian A k address =
  let target = FiniteReduction A k
      result = Solv.everySolvableMeridianImageTrivial
        target (finiteLevelHornActor A k) address
  in
    trans result (sym (reductionOfIdentity A k))
 
integralCongruenceHornMeridianTrivial :
  (A : SeparatedIntegralCongruenceActor) →
  ∀ address → meridianMatrix A address ≡ identityMatrix A
integralCongruenceHornMeridianTrivial A address =
  finiteReductionsSeparateMatrices A
    (meridianMatrix A address)
    (λ k → eachFiniteCongruenceKillsMeridian A k address)

-- For whole-group triviality the old MeridianGeneration owner
-- must still be instantiated for the actual geometric pi1.
