module Ontology.Hecke.LevelCorrespondenceRepresentation where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- The existing PrimeCorrespondenceHeckeOn is indexed by MonsterOntos.SSP,
-- which is exactly the fifteen Ogg-prime carrier.  That is appropriate for the
-- established SSP lane but cannot serve as an independent discovery/control
-- column: non-Ogg levels such as 9, 15, 21, 25, 27 and 33 are unrepresentable.
--
-- This module introduces the same finite "sum over correspondence class"
-- operator indexed by an arbitrary natural level.  Restricting a level-indexed
-- model along SSP -> Nat recovers the existing SSP-indexed interface exactly.
-- No converse extension is manufactured.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)

open import MonsterOntos using (SSP; toNat)
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
import Ontology.Hecke.CorrespondenceRepresentation as Existing

sum15 : Vec15 Nat → Nat
sum15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  a2 + a3 + a5 + a7 + a11 + a13 + a17 + a19 + a23 + a29 + a31 + a41 + a47 + a59 + a71

map15 : ∀ {A B : Set} → (A → B) → Vec15 A → Vec15 B
map15 f (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  mkVec15
    (f a2) (f a3) (f a5) (f a7) (f a11)
    (f a13) (f a17) (f a19) (f a23) (f a29)
    (f a31) (f a41) (f a47) (f a59) (f a71)

record LevelCorrespondenceHeckeOn (Class : Set) : Set₁ where
  field
    correspondence : Nat → Class → Vec15 Class

  operator : (Class → Nat) → Nat → Class → Nat
  operator f level x = sum15 (map15 f (correspondence level x))

open LevelCorrespondenceHeckeOn public

restrictLevelModelToSSP :
  ∀ {Class : Set} →
  LevelCorrespondenceHeckeOn Class →
  Existing.PrimeCorrespondenceHeckeOn Class
restrictLevelModelToSSP levelModel =
  record
    { correspondence =
        λ prime x → correspondence levelModel (toNat prime) x
    }

restrictionCorrespondenceExact :
  ∀ {Class : Set} →
  (levelModel : LevelCorrespondenceHeckeOn Class) →
  (prime : SSP) →
  (x : Class) →
  Existing.PrimeCorrespondenceHeckeOn.correspondence
    (restrictLevelModelToSSP levelModel) prime x
  ≡ correspondence levelModel (toNat prime) x
restrictionCorrespondenceExact levelModel prime x = refl

restrictionOperatorExact :
  ∀ {Class : Set} →
  (levelModel : LevelCorrespondenceHeckeOn Class) →
  (f : Class → Nat) →
  (prime : SSP) →
  (x : Class) →
  Existing.PrimeCorrespondenceHeckeOn.operator
    (restrictLevelModelToSSP levelModel) f prime x
  ≡ operator levelModel f (toNat prime) x
restrictionOperatorExact levelModel f prime x = refl

------------------------------------------------------------------------
-- Discovery boundary: an existing SSP-indexed model does not determine values
-- at arbitrary non-Ogg natural levels.  Such an extension must be supplied as
-- new mathematical data, not inferred from the fifteen-lane table.
------------------------------------------------------------------------

data SSPModelExtensionToAllLevels
  {Class : Set}
  (sspModel : Existing.PrimeCorrespondenceHeckeOn Class) : Set where
  extensionWitness :
    (levelModel : LevelCorrespondenceHeckeOn Class) →
    ((prime : SSP) →
      (x : Class) →
      correspondence levelModel (toNat prime) x
      ≡ Existing.PrimeCorrespondenceHeckeOn.correspondence sspModel prime x) →
    SSPModelExtensionToAllLevels sspModel
