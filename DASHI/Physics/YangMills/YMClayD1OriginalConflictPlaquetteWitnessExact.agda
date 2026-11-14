module DASHI.Physics.YangMills.YMClayD1OriginalConflictPlaquetteWitnessExact where

-- Constructively turn a failure of original plaquette-star disjointness
-- into an explicit ORIGINAL plaquette which contains both native bonds.
-- No physical distribution, locality estimate, or new axioms are used.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClayD1OriginalPeriodicPlaquetteFourBondSupportExact as Support
import DASHI.Physics.YangMills.YMClayD1OriginalPlaquetteSupportDecisionExact as Original

SharedOriginalPlaquette : ∀ {n} → Original.Bond n → Original.Bond n → Set
SharedOriginalPlaquette {n} a b =
  Σ (Plaquette.PeriodicPlaquette n)
    (λ p → Torus.Product
      (Torus._∈_ p (Original.originalIncidentPlaquettes a))
      (Torus._∈_ p (Original.originalIncidentPlaquettes b)))

-- Finite exhaustive search yields either an actual common plaquette
-- or the constructive proof that no common plaquette exists.
sharedOrDisjointOn :
  ∀ {n} (b : Original.Bond n)
    (ps : List (Plaquette.PeriodicPlaquette n)) →
  (Σ (Plaquette.PeriodicPlaquette n)
    (λ p → Torus.Product
      (Torus._∈_ p ps)
      (Torus._∈_ p (Original.originalIncidentPlaquettes b))))
  ⊎
  (∀ p → Torus._∈_ p ps →
    Torus._∈_ p (Original.originalIncidentPlaquettes b) → Torus.Empty)
sharedOrDisjointOn b [] = inj₂ (λ p ())
sharedOrDisjointOn b (p ∷ ps)
  with Original.decidePlaquetteIn p (Original.originalIncidentPlaquettes b)
... | Torus.yes member =
  inj₁ (p , Torus.pair Torus.here member)
... | Torus.no absent with sharedOrDisjointOn b ps
...   | inj₁ (q , witness) =
  inj₁ (q , Torus.pair
    (Torus.there (Torus.first witness))
    (Torus.second witness))
...   | inj₂ noShared =
  inj₂
    (λ { q Torus.here inB → absent inB
       ; q (Torus.there inTail) inB → noShared q inTail inB })

originalConflictExhibitsSharedPlaquette :
  ∀ {n} (a b : Original.Bond n) →
  (Original.OriginalStarsDisjoint a b → Torus.Empty) →
  SharedOriginalPlaquette a b
originalConflictExhibitsSharedPlaquette a b conflict
  with sharedOrDisjointOn b (Original.originalIncidentPlaquettes a)
... | inj₁ witness = witness
... | inj₂ disjoint = Original.emptyElim (conflict disjoint)

originalSharedPlaquetteHasBothNativeBonds :
  ∀ {n} (a b : Original.Bond n) →
  SharedOriginalPlaquette a b →
  Σ (Plaquette.PeriodicPlaquette n)
    (λ p → Torus.Product
      (Torus._∈_ a (Support.originalFourPositiveBonds p))
      (Torus._∈_ b (Support.originalFourPositiveBonds p)))
originalSharedPlaquetteHasBothNativeBonds a b (p , witness) =
  p , Torus.pair
    (Original.originalIncidentPlaquetteSound a p (Torus.first witness))
    (Original.originalIncidentPlaquetteSound b p (Torus.second witness))

originalNegativeConflictHasLiteralFourBondWitness :
  ∀ {n} (a b : Original.Bond n) →
  (Original.OriginalStarsDisjoint a b → Torus.Empty) →
  Σ (Plaquette.PeriodicPlaquette n)
    (λ p → Torus.Product
      (Torus._∈_ a (Support.originalFourPositiveBonds p))
      (Torus._∈_ b (Support.originalFourPositiveBonds p)))
originalNegativeConflictHasLiteralFourBondWitness a b notDisjoint =
  originalSharedPlaquetteHasBothNativeBonds a b
    (originalConflictExhibitsSharedPlaquette a b notDisjoint)


------------------------------------------------------------------------
-- End-to-end native greedy coverage certificate.
-- EVERY marked original bond is either selected by the greedy independent
-- set or is charged to an actual original plaquette shared with a
-- SELECTED bond. The latter witness is stronger than negative conflict.
------------------------------------------------------------------------

OriginalLiteralGreedyCoverage :
  ∀ {n} (marked : List (Original.Bond n))
    (b : Original.Bond n) → Set
OriginalLiteralGreedyCoverage {n} marked b =
  Torus._∈_ b (Original.greedyOriginalDisjointStars marked)
  ⊎
  Σ (Original.Bond n)
    (λ chosen → Torus.Product
      (Torus._∈_ chosen (Original.greedyOriginalDisjointStars marked))
      (Σ (Plaquette.PeriodicPlaquette n)
        (λ p → Torus.Product
          (Torus._∈_ chosen (Support.originalFourPositiveBonds p))
          (Torus._∈_ b (Support.originalFourPositiveBonds p)))))

originalGreedyMaximalityHasNativePlaquetteCoverage :
  ∀ {n} (marked : List (Original.Bond n))
    (b : Original.Bond n) →
  Torus._∈_ b marked →
  OriginalLiteralGreedyCoverage marked b
originalGreedyMaximalityHasNativePlaquetteCoverage marked b inMarked
  with Original.greedyOriginalDisjointStarsMaximal marked b inMarked
... | inj₁ selected = inj₁ selected
... | inj₂ (chosen , witness) =
  inj₂
    (chosen , Torus.pair
      (Torus.first witness)
      (originalNegativeConflictHasLiteralFourBondWitness
        chosen b (Torus.second witness)))
