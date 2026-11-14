module DASHI.Physics.Chemistry.AsymmetricChiralDynamicsIterationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics

------------------------------------------------------------------------
-- ITERATED MIRROR-EQUIVARIANT DYNAMICS
--
-- The first tranche proved the one-step commuting square.  This owner closes
-- the finite dynamical consequence: every iterate commutes with mirror, and the
-- five-state fixture reaches one of the two stable amplified branches (or the
-- racemic fixed point) after at most one positive step.
------------------------------------------------------------------------

iterate : {A : Set} → Nat → (A → A) → A → A
iterate zero f x = x
iterate (suc n) f x = f (iterate n f x)

iterateMirrorEquivariant :
  (D : Dynamics.MirrorEquivariantDynamics) →
  (n : Nat) →
  (x : Dynamics.State D) →
  iterate n (Dynamics.step D) (Dynamics.mirror D x)
    ≡ Dynamics.mirror D (iterate n (Dynamics.step D) x)
iterateMirrorEquivariant D zero x = refl
iterateMirrorEquivariant D (suc n) x =
  trans
    (cong (Dynamics.step D) (iterateMirrorEquivariant D n x))
    (Dynamics.stepMirrorEquivariant D
      (iterate n (Dynamics.step D) x))

leftAmplifiedStable :
  (n : Nat) →
  iterate n Dynamics.amplifyBias Dynamics.leftAmplified
    ≡ Dynamics.leftAmplified
leftAmplifiedStable zero = refl
leftAmplifiedStable (suc n) =
  trans
    (cong Dynamics.amplifyBias (leftAmplifiedStable n))
    Dynamics.leftAmplifiedFixed

rightAmplifiedStable :
  (n : Nat) →
  iterate n Dynamics.amplifyBias Dynamics.rightAmplified
    ≡ Dynamics.rightAmplified
rightAmplifiedStable zero = refl
rightAmplifiedStable (suc n) =
  trans
    (cong Dynamics.amplifyBias (rightAmplifiedStable n))
    Dynamics.rightAmplifiedFixed

racemicStable :
  (n : Nat) →
  iterate n Dynamics.amplifyBias Dynamics.racemic
    ≡ Dynamics.racemic
racemicStable zero = refl
racemicStable (suc n) =
  trans
    (cong Dynamics.amplifyBias (racemicStable n))
    Dynamics.racemicDynamicallyFixed

leftSeedReachesStableBranch :
  (n : Nat) →
  iterate (suc n) Dynamics.amplifyBias Dynamics.leftSeed
    ≡ Dynamics.leftAmplified
leftSeedReachesStableBranch zero = Dynamics.leftSeedAmplifies
leftSeedReachesStableBranch (suc n) =
  trans
    (cong Dynamics.amplifyBias (leftSeedReachesStableBranch n))
    Dynamics.leftAmplifiedFixed

rightSeedReachesStableBranch :
  (n : Nat) →
  iterate (suc n) Dynamics.amplifyBias Dynamics.rightSeed
    ≡ Dynamics.rightAmplified
rightSeedReachesStableBranch zero = Dynamics.rightSeedAmplifies
rightSeedReachesStableBranch (suc n) =
  trans
    (cong Dynamics.amplifyBias (rightSeedReachesStableBranch n))
    Dynamics.rightAmplifiedFixed

finiteIteratesRemainMirrorEquivariant :
  (n : Nat) →
  (x : Dynamics.ChiralBiasState) →
  iterate n Dynamics.amplifyBias (Dynamics.mirrorBias x)
    ≡ Dynamics.mirrorBias (iterate n Dynamics.amplifyBias x)
finiteIteratesRemainMirrorEquivariant =
  iterateMirrorEquivariant Dynamics.finiteChiralDynamics

record IteratedChiralDynamicsBoundary : Set where
  constructor iteratedChiralDynamicsBoundary
  field
    oneStepEquivarianceExtendsToAllFiniteIterates : Bool
    amplifiedBranchesAreFiniteFixedPoints : Bool
    racemicStateIsFiniteFixedPoint : Bool
    everyNonracemicSeedReachesItsAmplifiedBranchAfterPositiveTime : Bool
    finiteAttractorFixtureIsContinuousKineticConvergenceTheorem : Bool

canonicalIteratedChiralDynamicsBoundary : IteratedChiralDynamicsBoundary
canonicalIteratedChiralDynamicsBoundary =
  iteratedChiralDynamicsBoundary true true true true false
