module DASHI.Mathematics.Topology.AlexanderHornedProPSolvableBlindExact where

------------------------------------------------------------------------
-- NO-GO: COMPATIBLE HORN MERIDIAN ACTIONS INTO ANY SOLVABLE TARGET.
--
-- Source: Hatcher Example 2B.2 injective commutator tower;
-- classical theorem finite p-groups are solvable.
--
-- New exact theorem: for a target with an EXPLICIT finite
-- derived/commutator filtration, ANY horn-meridian assignment
-- respecting the literal recursive commutator relation vanishes.
--
-- This strengthens the repo's prior
--   AlexanderHornedAbelianHolonomyBIDIExact
-- from derived length ONE (abelian) to ARBITRARY finite
-- derived length. It is not just a Boolean status flag.
--
-- In particular any map from the abstract perfect horned group
-- to any finite p-group is trivial. Its pro-p completion is
-- consequently trivial. A5 quotients and matrix representations
-- over Q_p are NONABELIAN and are not prohibited.
--
-- A concrete p-group constructor and full geometric fundamental
-- group are not built here. Finite-p-group solvability is a cited
-- external theorem; a target must PROVIDE its filtration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn

record SolvableCommutatorTarget : Set₁ where
  field
    Carrier : Set
    identity : Carrier
    commutator : Carrier → Carrier → Carrier

    Derived : Nat → Carrier → Set
    derivedZero : ∀ x → Derived zero x
    derivedCommutator : ∀ n a b →
      Derived n a → Derived n b →
      Derived (suc n) (commutator a b)

    derivedLength : Nat
    derivedLengthTrivial : ∀ x →
      Derived derivedLength x → x ≡ identity

open SolvableCommutatorTarget public

record HornMeridianRepresentation
    (T : SolvableCommutatorTarget) : Set where
  field
    image : Horn.HornAddress → Carrier T
    respectsRecursiveCommutator : ∀ address →
      image address ≡ commutator T
        (image (Horn.leftChild address))
        (image (Horn.rightChild address))

open HornMeridianRepresentation public

-- Induction applies recursively to ALL addresses, which is why no
-- finite truncation or numerical certificate is being substituted
-- for an infinite-group claim.
everyMeridianImageInEveryDerivedLevel :
  (T : SolvableCommutatorTarget) →
  (rho : HornMeridianRepresentation T) →
  ∀ n address → Derived T n (image rho address)
everyMeridianImageInEveryDerivedLevel T rho zero address =
  derivedZero T (image rho address)
everyMeridianImageInEveryDerivedLevel T rho (suc n) address =
  subst
    (Derived T (suc n))
    (sym (respectsRecursiveCommutator rho address))
    (derivedCommutator T n
      (image rho (Horn.leftChild address))
      (image rho (Horn.rightChild address))
      (everyMeridianImageInEveryDerivedLevel T rho
        n (Horn.leftChild address))
      (everyMeridianImageInEveryDerivedLevel T rho
        n (Horn.rightChild address)))

everySolvableMeridianImageTrivial :
  (T : SolvableCommutatorTarget) →
  (rho : HornMeridianRepresentation T) →
  ∀ address → image rho address ≡ identity T
everySolvableMeridianImageTrivial T rho address =
  derivedLengthTrivial T (image rho address)
    (everyMeridianImageInEveryDerivedLevel T rho
      (derivedLength T) address)

-- To promote 'all meridians vanish' to an arbitrary group element
-- requires the existing explicit MeridianGeneration certificate.
-- An arbitrary nonabelian p-adic matrix group does not supply a
-- terminating derived filtration, so the theorem does not block
-- our A5 regular permutation matrices over Q_p.
