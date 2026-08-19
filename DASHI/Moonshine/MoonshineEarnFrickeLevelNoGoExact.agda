module DASHI.Moonshine.MoonshineEarnFrickeLevelNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7.
-- No DOI asserted.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bull. London Math. Soc. 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- SOURCE ROLE
--
-- The Fricke involution W_p acts on the prime-level modular curve X_0(p):
-- it reverses the p-isogeny / cyclic subgroup datum but does not change p.
--
-- DASHI CONTRIBUTION
--
-- Make level preservation part of the TYPE.  A lifted Fricke action on a
-- level-tagged point preserves the level definitionally.  Therefore the PR #1
-- arithmetic substitutions
--
--   23 -> 47,  7 -> 59,  11 -> 71
--
-- cannot literally be Fricke involutions or Fricke orbit motion.  This is
-- independent of whether all six levels happen to lie on the genus-zero locus.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Generic prime/level-indexed Fricke family.
------------------------------------------------------------------------

record LevelIndexedFrickeFamily : Set₁ where
  field
    Point : Nat → Set
    fricke : (level : Nat) → Point level → Point level
    frickeInvolutive :
      (level : Nat) → (point : Point level) →
      fricke level (fricke level point) ≡ point

open LevelIndexedFrickeFamily public

record TaggedFrickePoint (F : LevelIndexedFrickeFamily) : Set where
  constructor tagged-fricke-point
  field
    level : Nat
    point : Point F level

open TaggedFrickePoint public

liftFricke :
  (F : LevelIndexedFrickeFamily) →
  TaggedFrickePoint F → TaggedFrickePoint F
liftFricke F q =
  tagged-fricke-point
    (level q)
    (fricke F (level q) (point q))

liftFrickePreservesLevel :
  (F : LevelIndexedFrickeFamily) →
  (q : TaggedFrickePoint F) →
  level (liftFricke F q) ≡ level q
liftFrickePreservesLevel F q = refl

------------------------------------------------------------------------
-- A claimed cross-level interpretation must therefore identify source and
-- target levels.  The historical pairs are definitionally distinct.
------------------------------------------------------------------------

record FrickeLevelSubstitution
    (F : LevelIndexedFrickeFamily)
    (sourceLevel targetLevel : Nat) : Set where
  field
    sourcePoint : Point F sourceLevel
    targetLevelExact :
      level
        (liftFricke F
          (tagged-fricke-point sourceLevel sourcePoint))
      ≡ targetLevel

open FrickeLevelSubstitution public

frickeSubstitutionForcesSameLevel :
  (F : LevelIndexedFrickeFamily) →
  (sourceLevel targetLevel : Nat) →
  FrickeLevelSubstitution F sourceLevel targetLevel →
  sourceLevel ≡ targetLevel
frickeSubstitutionForcesSameLevel F sourceLevel targetLevel W =
  targetLevelExact W

historical23To47CannotBeFrickeMotion :
  (F : LevelIndexedFrickeFamily) →
  FrickeLevelSubstitution F 23 47 → ⊥
historical23To47CannotBeFrickeMotion F W
  with frickeSubstitutionForcesSameLevel F 23 47 W
... | ()

historical7To59CannotBeFrickeMotion :
  (F : LevelIndexedFrickeFamily) →
  FrickeLevelSubstitution F 7 59 → ⊥
historical7To59CannotBeFrickeMotion F W
  with frickeSubstitutionForcesSameLevel F 7 59 W
... | ()

historical11To71CannotBeFrickeMotion :
  (F : LevelIndexedFrickeFamily) →
  FrickeLevelSubstitution F 11 71 → ⊥
historical11To71CannotBeFrickeMotion F W
  with frickeSubstitutionForcesSameLevel F 11 71 W
... | ()

record MoonshineEarnFrickeLevelNoGoBoundary : Set where
  field
    levelIndexedFrickeCarrierUsed : Bool
    levelPreservationDerivedDefinitionally : Bool
    historical23To47Rejected : Bool
    historical7To59Rejected : Bool
    historical11To71Rejected : Bool
    directFrickeInvolutionExplanationPossible : Bool
    genusZeroCoincidenceStillCompatible : Bool

canonicalMoonshineEarnFrickeLevelNoGoBoundary :
  MoonshineEarnFrickeLevelNoGoBoundary
canonicalMoonshineEarnFrickeLevelNoGoBoundary = record
  { levelIndexedFrickeCarrierUsed = true
  ; levelPreservationDerivedDefinitionally = true
  ; historical23To47Rejected = true
  ; historical7To59Rejected = true
  ; historical11To71Rejected = true
  ; directFrickeInvolutionExplanationPossible = false
  ; genusZeroCoincidenceStillCompatible = true
  }
