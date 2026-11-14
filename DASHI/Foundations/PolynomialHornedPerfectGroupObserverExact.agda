module DASHI.Foundations.PolynomialHornedPerfectGroupObserverExact where

------------------------------------------------------------------------
-- PERFECT GROUPS / ABELIAN BLINDNESS, GENERIC CONSTRUCTIVE THEOREM.
--
-- Prior art: Hatcher, Algebraic Topology Example 2B.2 (classical horn
-- exterior), Galois/Jordan for A5, and perfect binary icosahedral 2I.
-- This adapter never identifies the three groups or their source loops.
--
-- We use the mathematically correct "product of commutators" witness;
-- perfection DOES NOT assert every element is a SINGLE commutator.
-- The original Hatcher PR #1244 and Pickover PR #1260 remain independent
-- draft donors. No import of PR-only objects from the other branches.
--
-- Concrete supplied decomposition + target-homorphism laws entail
-- triviality of EVERY homomorphism into an Abelian target; in fact the
-- target need not be Abelian once the commutator-killing law is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

record CommutatorGeneratedGroup : Set₁ where
  field
    Carrier : Set
    identity : Carrier
    multiply : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier
    decomposition : Carrier → List (Carrier × Carrier)

  commutator : Carrier → Carrier → Carrier
  commutator a b =
    multiply
      (multiply
        (multiply a b)
        (inverse a))
      (inverse b)

  foldCommutators : List (Carrier × Carrier) → Carrier
  foldCommutators [] = identity
  foldCommutators ((a , b) ∷ xs) =
    multiply (commutator a b) (foldCommutators xs)

  field
    reconstruct :
      (g : Carrier) →
      foldCommutators (decomposition g) ≡ g

open CommutatorGeneratedGroup public

record CommutatorKillingObserver (S : CommutatorGeneratedGroup) : Set₁ where
  field
    Target : Set
    targetIdentity : Target
    targetMultiply : Target → Target → Target
    observe : Carrier S → Target

    mapIdentity : observe (identity S) ≡ targetIdentity
    mapProduct :
      (a b : Carrier S) →
      observe (multiply S a b)
      ≡ targetMultiply (observe a) (observe b)

    killCommutator :
      (a b : Carrier S) →
      observe (commutator S a b) ≡ targetIdentity

    targetUnitLeft : (t : Target) →
      targetMultiply targetIdentity t ≡ t

open CommutatorKillingObserver public

foldCommutatorImageIsIdentity :
  (S : CommutatorGeneratedGroup)
  (O : CommutatorKillingObserver S)
  (xs : List (Carrier S × Carrier S)) →
  observe O (foldCommutators S xs) ≡ targetIdentity O
foldCommutatorImageIsIdentity S O [] = mapIdentity O
foldCommutatorImageIsIdentity S O ((a , b) ∷ xs) =
  trans
    (mapProduct O (commutator S a b) (foldCommutators S xs))
    (trans
      (cong₂ (targetMultiply O)
        (killCommutator O a b)
        (foldCommutatorImageIsIdentity S O xs))
      (targetUnitLeft O (targetIdentity O)))

everyCommutatorGeneratedGroupAbelianObserverIsTrivial :
  (S : CommutatorGeneratedGroup)
  (O : CommutatorKillingObserver S)
  (g : Carrier S) →
  observe O g ≡ targetIdentity O
everyCommutatorGeneratedGroupAbelianObserverIsTrivial S O g =
  trans
    (cong (observe O) (sym (reconstruct S g)))
    (foldCommutatorImageIsIdentity S O (decomposition S g))

-- LEGITIMATE CROSS-POLLINATION RECEIVERS (uninstantiated here):
--
-- A5: the commutator subgroup is all A5; group-exhaustion donor #1244.
-- 2I: the perfect 120-element binary icosahedral spin group, #1244.
-- G_A * G_A * G_A: the abstract Hatcher meridian direct-limit group,
--   #1244, provided a genuine group presentation/colimit and witness.
--
-- The picked SOURCE GROUP must be the same object throughout any
-- observer calculation. The theorem does not identify G_A, A5 and 2I.
