{-# OPTIONS --safe #-}
module DASHI.Core.MereologyNonCollapseExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- FINITE COUNTERMODELS FOR THE MEREOLOGICAL NON-COLLAPSE LAWS
------------------------------------------------------------------------

data Atom : Set where
  left right : Atom

data PartOf : Atom → Atom → Set where
  leftPartOfRight : PartOf left right

data SubclassOf : Atom → Atom → Set where

data InstanceOf : Atom → Atom → Set where

¬_ : Set → Set
¬ A = A → ⊥

partOfDoesNotImplySubclass :
  ¬ ((x y : Atom) → PartOf x y → SubclassOf x y)
partOfDoesNotImplySubclass collapse =
  collapse left right leftPartOfRight

partOfDoesNotImplyInstance :
  ¬ ((x y : Atom) → PartOf x y → InstanceOf x y)
partOfDoesNotImplyInstance collapse =
  collapse left right leftPartOfRight

Overlap : Atom → Atom → Set
Overlap _ _ = ⊤

Compatible : Atom → Atom → Set
Compatible left left = ⊤
Compatible right right = ⊤
Compatible left right = ⊥
Compatible right left = ⊥

leftRightOverlap :
  Overlap left right
leftRightOverlap = tt

leftRightNotCompatible :
  ¬ Compatible left right
leftRightNotCompatible ()

overlapDoesNotImplyCompatibility :
  ¬ ((x y : Atom) → Overlap x y → Compatible x y)
overlapDoesNotImplyCompatibility collapse =
  leftRightNotCompatible (collapse left right tt)

------------------------------------------------------------------------
-- Equal consumer observation does not identify wholes.
------------------------------------------------------------------------

data Whole : Set where
  wholeA wholeB : Whole

observe : Whole → ⊤
observe _ = tt

observationsEqual :
  observe wholeA ≡ observe wholeB
observationsEqual = refl

wholeADistinctFromWholeB :
  ¬ (wholeA ≡ wholeB)
wholeADistinctFromWholeB ()

equalProjectionDoesNotImplyWholeEquality :
  ¬ ((x y : Whole) → observe x ≡ observe y → x ≡ y)
equalProjectionDoesNotImplyWholeEquality collapse =
  wholeADistinctFromWholeB
    (collapse wholeA wholeB observationsEqual)

------------------------------------------------------------------------
-- Pairwise local compatibility alone does not manufacture global descent.
------------------------------------------------------------------------

data LocalPart : Set where
  p0 p1 p2 : LocalPart

PairCompatible : LocalPart → LocalPart → Set
PairCompatible _ _ = ⊤

record PairwiseCompatible : Set where
  constructor pairwise-compatible
  field
    c01 : PairCompatible p0 p1
    c12 : PairCompatible p1 p2
    c20 : PairCompatible p2 p0

canonicalPairwiseCompatible : PairwiseCompatible
canonicalPairwiseCompatible =
  pairwise-compatible tt tt tt

data GlobalFusionReceipt : Set where

pairwiseCompatibilityDoesNotCreateGlobalFusion :
  PairwiseCompatible →
  ¬ GlobalFusionReceipt
pairwiseCompatibilityDoesNotCreateGlobalFusion _ ()
