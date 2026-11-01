module DASHI.Philosophy.MarkedRelationalExtension where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Philosophy.LocalChartNormalisation as Local

------------------------------------------------------------------------
-- Nine is a declared interior, ten is a marked standpoint, and eleven adds a
-- distinguishable relational degree.  This is a modelling convention, not a
-- theorem that arithmetic alone creates relation.

record MarkedRelationalExtension
       (X Relation : Set) : Set₁ where
  field
    interior :
      List X

    star :
      X

    selfUnit :
      X

    other :
      X

    relation :
      Relation

    starNormalisesToSelf :
      Set

    selfAndOtherRemainDistinct :
      Set

    relationIsAdditionalStructure :
      Set

    arithmeticNecessitatesPhilosophicalMeaning :
      Bool

open MarkedRelationalExtension public

globalMarkedIndex : Nat
globalMarkedIndex =
  Local.globalStarIndex

relationalMarkedIndex : Nat
relationalMarkedIndex =
  Local.relationalExtensionIndex

globalMarkedIndexIsTen :
  globalMarkedIndex ≡ 10
globalMarkedIndexIsTen =
  refl

relationalMarkedIndexIsEleven :
  relationalMarkedIndex ≡ 11
relationalMarkedIndexIsEleven =
  refl

record RelationalDegreeBoundary : Set where
  constructor mkRelationalDegreeBoundary
  field
    localSelfIdentity :
      Bool

    additionalOtherPosition :
      Bool

    relationExplicit :
      Bool

    numericalDestinyClaimed :
      Bool

open RelationalDegreeBoundary public

canonicalRelationalDegreeBoundary :
  RelationalDegreeBoundary
canonicalRelationalDegreeBoundary =
  mkRelationalDegreeBoundary
    true
    true
    true
    false

canonicalNoNumericalDestiny :
  numericalDestinyClaimed canonicalRelationalDegreeBoundary
  ≡
  false
canonicalNoNumericalDestiny =
  refl
