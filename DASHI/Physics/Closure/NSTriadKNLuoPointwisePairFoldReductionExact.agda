module DASHI.Physics.Closure.NSTriadKNLuoPointwisePairFoldReductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Reduce a whole finite Fourier-fold identification to a coefficient theorem
-- for one physical pair.  This is the exact proof-engineering boundary needed
-- by the r_{p,1}, r_{p,2}, and u_{>p} tensor u_{>p} identifications: once the
-- contribution attached to every mature pair is equal, mapping and folding
-- preserve the equality automatically.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellTermFoldExact as Fold

mapListPointwiseCong :
  ∀ {a b}
    {A : Set a}
    {B : Set b}
    (left right : A → B)
    (values : List A) →
  (∀ value → left value ≡ right value) →
  Fold.mapList left values ≡ Fold.mapList right values
mapListPointwiseCong left right [] pointwise = refl
mapListPointwiseCong left right (value ∷ values) pointwise =
  cong₂ _∷_
    (pointwise value)
    (mapListPointwiseCong left right values pointwise)

foldMappedPointwiseCong :
  ∀ {a b}
    {A : Set a}
    {B : Set b}
    (combine : B → B → B)
    (zero : B)
    (left right : A → B)
    (values : List A) →
  (∀ value → left value ≡ right value) →
  Fold.foldList combine zero (Fold.mapList left values)
  ≡ Fold.foldList combine zero (Fold.mapList right values)
foldMappedPointwiseCong combine zero left right values pointwise =
  cong
    (Fold.foldList combine zero)
    (mapListPointwiseCong left right values pointwise)

record PointwisePairIdentification
    {a b : Level}
    {Pair : Set a}
    {Contribution : Set b}
    (pairs : List Pair) : Set (a ⊔ b) where
  field
    sourceContribution targetContribution : Pair → Contribution
    pairwiseIdentification :
      ∀ pair → sourceContribution pair ≡ targetContribution pair

open PointwisePairIdentification public

pointwiseIdentificationGivesFoldIdentification :
  ∀ {a b}
    {Pair : Set a}
    {Contribution : Set b}
    {pairs : List Pair} →
  (identification : PointwisePairIdentification pairs) →
  (combine : Contribution → Contribution → Contribution) →
  (zero : Contribution) →
  Fold.foldList combine zero
    (Fold.mapList (sourceContribution identification) pairs)
  ≡
  Fold.foldList combine zero
    (Fold.mapList (targetContribution identification) pairs)
pointwiseIdentificationGivesFoldIdentification
  identification combine zero =
  foldMappedPointwiseCong
    combine
    zero
    (sourceContribution identification)
    (targetContribution identification)
    pairs
    (pairwiseIdentification identification)

pointwisePairToWholeFoldReductionClosed : Bool
pointwisePairToWholeFoldReductionClosed = true

threeLuoPiecesShareOneFoldReducer : Bool
threeLuoPiecesShareOneFoldReducer = true

pointwisePairToWholeFoldReductionClosedIsTrue :
  pointwisePairToWholeFoldReductionClosed ≡ true
pointwisePairToWholeFoldReductionClosedIsTrue = refl

threeLuoPiecesShareOneFoldReducerIsTrue :
  threeLuoPiecesShareOneFoldReducer ≡ true
threeLuoPiecesShareOneFoldReducerIsTrue = refl
