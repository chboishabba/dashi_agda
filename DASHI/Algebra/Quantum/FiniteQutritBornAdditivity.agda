module DASHI.Algebra.Quantum.FiniteQutritBornAdditivity where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)

import DASHI.Algebra.Quantum.FiniteTreeWeyl as Tree

------------------------------------------------------------------------
-- Exact finite Pythagorean/Born additivity for disjoint qutrit basis states.

addAmplitude : Tree.Amplitude → Tree.Amplitude → Tree.Amplitude
addAmplitude left right q = left q + right q


data DistinctQutrit : Tree.Qutrit → Tree.Qutrit → Set where
  q0-q1 : DistinctQutrit Tree.q0 Tree.q1
  q0-q2 : DistinctQutrit Tree.q0 Tree.q2
  q1-q0 : DistinctQutrit Tree.q1 Tree.q0
  q1-q2 : DistinctQutrit Tree.q1 Tree.q2
  q2-q0 : DistinctQutrit Tree.q2 Tree.q0
  q2-q1 : DistinctQutrit Tree.q2 Tree.q1

basisBornAdditivity :
  ∀ {left right} →
  DistinctQutrit left right →
  Tree.normSquared
    (addAmplitude (Tree.basisAmplitude left) (Tree.basisAmplitude right))
  ≡ Tree.normSquared (Tree.basisAmplitude left)
    + Tree.normSquared (Tree.basisAmplitude right)
basisBornAdditivity q0-q1 = refl
basisBornAdditivity q0-q2 = refl
basisBornAdditivity q1-q0 = refl
basisBornAdditivity q1-q2 = refl
basisBornAdditivity q2-q0 = refl
basisBornAdditivity q2-q1 = refl

record FiniteQutritBornAdditivityReceipt : Set where
  constructor finite-qutrit-born-additivity
  field
    disjointBasisAdditivity :
      ∀ {left right} →
      DistinctQutrit left right →
      Tree.normSquared
        (addAmplitude
          (Tree.basisAmplitude left)
          (Tree.basisAmplitude right))
      ≡ Tree.normSquared (Tree.basisAmplitude left)
        + Tree.normSquared (Tree.basisAmplitude right)
open FiniteQutritBornAdditivityReceipt public

canonicalFiniteQutritBornAdditivityReceipt :
  FiniteQutritBornAdditivityReceipt
canonicalFiniteQutritBornAdditivityReceipt =
  finite-qutrit-born-additivity basisBornAdditivity
