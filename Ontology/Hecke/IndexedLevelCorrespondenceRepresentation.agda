module Ontology.Hecke.IndexedLevelCorrespondenceRepresentation where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Extend LevelCorrespondenceRepresentation to a level-dependent class family
--
--   Class : Nat -> Set.
--
-- This is required by the representation-first SSP lane: a candidate-indexed
-- restriction such as V_j downarrow D_(2j+1) naturally has a different finite
-- sector carrier at each level.  Forcing every level into one fixed class type
-- would erase that dependency before the actual intertwiner is constructed.
--
-- A fixed-class LevelCorrespondenceHeckeOn embeds definitionally as the
-- constant-family special case.  No Ogg list or exceptional predicate enters
-- this carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Ontology.GodelLattice using (Vec15)

import Ontology.Hecke.LevelCorrespondenceRepresentation as Level

record IndexedLevelCorrespondenceHeckeOn
    (Class : Nat → Set) : Set₁ where
  field
    correspondence :
      (level : Nat) → Class level → Vec15 (Class level)

  operator :
    (level : Nat) →
    (Class level → Nat) →
    Class level → Nat
  operator level observable state =
    Level.sum15
      (Level.map15 observable (correspondence level state))

open IndexedLevelCorrespondenceHeckeOn public

constantClass : Set → Nat → Set
constantClass Class level = Class

fromFixedLevelModel :
  ∀ {Class : Set} →
  Level.LevelCorrespondenceHeckeOn Class →
  IndexedLevelCorrespondenceHeckeOn (constantClass Class)
fromFixedLevelModel fixed =
  record
    { correspondence =
        λ level state → Level.correspondence fixed level state
    }

fromFixedCorrespondenceExact :
  ∀ {Class : Set}
    (fixed : Level.LevelCorrespondenceHeckeOn Class)
    (level : Nat)
    (state : Class) →
  correspondence (fromFixedLevelModel fixed) level state
  ≡ Level.correspondence fixed level state
fromFixedCorrespondenceExact fixed level state = refl

fromFixedOperatorExact :
  ∀ {Class : Set}
    (fixed : Level.LevelCorrespondenceHeckeOn Class)
    (level : Nat)
    (observable : Class → Nat)
    (state : Class) →
  operator (fromFixedLevelModel fixed) level observable state
  ≡ Level.operator fixed observable level state
fromFixedOperatorExact fixed level observable state = refl
