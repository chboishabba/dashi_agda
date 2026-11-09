module DASHI.Moonshine.Y443Original72Plus8RelatorSatisfactionExact where

------------------------------------------------------------------------
-- EXACT SOURCE-PRESERVING Y443 RELATOR SATISFACTION SPLIT.
--
-- The 80 literal original relators are split by ORIGINAL SOURCE INDEX,
-- not by a newly axiomatized 72/8 presentation.  Four node squares,
-- three graph-edge cubes and the original central relator are assigned
-- to the eight-element complement.  All other words stay in the
-- 72-element part, in original order.
--
-- The original group RelatorsSatisfied is CONSTRUCTIVELY equivalent
-- to satisfaction of BOTH partitioned lists. This applies to every
-- original GroupWithInverse and node interpretation, not only C2.
--
-- Source attribution: Ivanov/Bray presentation, DASHI exact word owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.TwistedModuleModularity as TM

-- Index positions in the original coxeter squares ++ pair words
-- ++ spider ++ central enumeration, all ZERO-BASED:
-- squares e2,b3,c3,d3 = 8,9,10,11
-- edge words d2-e2,b3-c3,c3-d3 = 68,75,77
-- final central word = 79.
-- Unlike a synthetic 72/8 split, these are literal source positions.
residualAt : Nat → Bool
residualAt 8 = true
residualAt 9 = true
residualAt 10 = true
residualAt 11 = true
residualAt 68 = true
residualAt 75 = true
residualAt 77 = true
residualAt 79 = true
residualAt _ = false

partitionAt :
  Nat → List Y.Word → List Y.Word × List Y.Word
partitionAt index [] = [] , []
partitionAt index (w ∷ words) with residualAt index
... | true =
  let rest = partitionAt (suc index) words in
  proj₁ rest , (w ∷ proj₂ rest)
... | false =
  let rest = partitionAt (suc index) words in
  (w ∷ proj₁ rest) , proj₂ rest

original72 : List Y.Word
original72 = proj₁ (partitionAt zero Y.monsterRelators)

original8 : List Y.Word
original8 = proj₂ (partitionAt zero Y.monsterRelators)

source72Count : Y.length original72 ≡ 72
source72Count = refl

source8Count : Y.length original8 ≡ 8
source8Count = refl

-- These two directions are formalized over THE SAME actual source
-- predicate (Pair.RelatorsSatisfied), not a weaker Boolean check.
module UnderOriginalGroup
  {G : Set}
  (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G) where

  splitAll :
    (index : Nat) (words : List Y.Word) →
    Pair.RelatorsSatisfied gi nodes words →
    Pair.RelatorsSatisfied gi nodes (proj₁ (partitionAt index words))
      × Pair.RelatorsSatisfied gi nodes
          (proj₂ (partitionAt index words))
  splitAll index [] satisfied = tt , tt
  splitAll index (w ∷ words) satisfied
    with residualAt index
  ... | true =
    let rest = splitAll (suc index) words (Pair._∧_.right satisfied)
    in proj₁ rest ,
       Pair._,,_ (Pair._∧_.left satisfied) (proj₂ rest)
  ... | false =
    let rest = splitAll (suc index) words (Pair._∧_.right satisfied)
    in Pair._,,_ (Pair._∧_.left satisfied) (proj₁ rest) ,
       proj₂ rest

  mergeAll :
    (index : Nat) (words : List Y.Word) →
    Pair.RelatorsSatisfied gi nodes (proj₁ (partitionAt index words)) →
    Pair.RelatorsSatisfied gi nodes (proj₂ (partitionAt index words)) →
    Pair.RelatorsSatisfied gi nodes words
  mergeAll index [] left right = tt
  mergeAll index (w ∷ words) left right
    with residualAt index
  ... | true =
    Pair._,,_
      (Pair._∧_.left right)
      (mergeAll (suc index) words
        left (Pair._∧_.right right))
  ... | false =
    Pair._,,_
      (Pair._∧_.left left)
      (mergeAll (suc index) words
        (Pair._∧_.right left) right)

  original80ImpliesOriginal72And8 :
    Pair.RelatorsSatisfied gi nodes Y.monsterRelators →
    Pair.RelatorsSatisfied gi nodes original72
      × Pair.RelatorsSatisfied gi nodes original8
  original80ImpliesOriginal72And8 =
    splitAll zero Y.monsterRelators

  original72And8ImplyOriginal80 :
    Pair.RelatorsSatisfied gi nodes original72 →
    Pair.RelatorsSatisfied gi nodes original8 →
    Pair.RelatorsSatisfied gi nodes Y.monsterRelators
  original72And8ImplyOriginal80 =
    mergeAll zero Y.monsterRelators

  roundTrip80 :
    (h : Pair.RelatorsSatisfied gi nodes Y.monsterRelators) →
    Pair.RelatorsSatisfied gi nodes Y.monsterRelators
  roundTrip80 h =
    original72And8ImplyOriginal80
      (proj₁ (original80ImpliesOriginal72And8 h))
      (proj₂ (original80ImpliesOriginal72And8 h))
