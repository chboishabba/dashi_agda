module DASHI.Physics.Closure.NSTriadKNNineOwnerDualNoGoRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal für die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- DASHI CONTRIBUTION
--
-- Round 37 introduced a certified primal minimizer for the nine-owner reserve.
-- The continuation analysis asks for the equally important failure witness:
-- if no strict reserve exists, do not trust a numerical optimizer -- produce
-- an exact rational dual certificate.
--
-- This module gives a finite nine-coordinate Farkas/LP-duality certificate.
-- A physical constraint has the form
--
--   b_j <= a_j . eta.
--
-- A dual cell carries a nonnegative multiplier lambda_j.  If the weighted
-- normals sum exactly to the all-ones vector and the weighted lower bounds
-- sum to at least one, then every point satisfying all constraints obeys
--
--   1 <= eta_1 + ... + eta_9.
--
-- Therefore a failed owner architecture can be accompanied by a small exact
-- rational proof object.  Numerical search may discover lambda_j; Agda only
-- checks the rational inequalities and coefficient identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

record NineVector : Set where
  constructor nine-vector
  field
    x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℚ

open NineVector public

zeroVector onesVector : NineVector
zeroVector = nine-vector 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ
onesVector = nine-vector 1ℚ 1ℚ 1ℚ 1ℚ 1ℚ 1ℚ 1ℚ 1ℚ 1ℚ

vectorAdd : NineVector → NineVector → NineVector
vectorAdd left right = nine-vector
  (x1 left + x1 right)
  (x2 left + x2 right)
  (x3 left + x3 right)
  (x4 left + x4 right)
  (x5 left + x5 right)
  (x6 left + x6 right)
  (x7 left + x7 right)
  (x8 left + x8 right)
  (x9 left + x9 right)

vectorScale : ℚ → NineVector → NineVector
vectorScale scalar value = nine-vector
  (scalar * x1 value)
  (scalar * x2 value)
  (scalar * x3 value)
  (scalar * x4 value)
  (scalar * x5 value)
  (scalar * x6 value)
  (scalar * x7 value)
  (scalar * x8 value)
  (scalar * x9 value)

vectorExt : ∀ {left right : NineVector} →
  x1 left ≡ x1 right → x2 left ≡ x2 right →
  x3 left ≡ x3 right → x4 left ≡ x4 right →
  x5 left ≡ x5 right → x6 left ≡ x6 right →
  x7 left ≡ x7 right → x8 left ≡ x8 right →
  x9 left ≡ x9 right → left ≡ right
vectorExt
  {nine-vector a1 a2 a3 a4 a5 a6 a7 a8 a9}
  {nine-vector .a1 .a2 .a3 .a4 .a5 .a6 .a7 .a8 .a9}
  refl refl refl refl refl refl refl refl refl = refl

dot : NineVector → NineVector → ℚ
dot left right =
  x1 left * x1 right + x2 left * x2 right
  + x3 left * x3 right + x4 left * x4 right
  + x5 left * x5 right + x6 left * x6 right
  + x7 left * x7 right + x8 left * x8 right
  + x9 left * x9 right

etaTotal : NineVector → ℚ
etaTotal eta =
  x1 eta + x2 eta + x3 eta + x4 eta + x5 eta
  + x6 eta + x7 eta + x8 eta + x9 eta

dotOnesIsEtaTotal : ∀ eta → dot onesVector eta ≡ etaTotal eta
dotOnesIsEtaTotal eta = solve
  ( x1 eta ∷ x2 eta ∷ x3 eta ∷ x4 eta ∷ x5 eta
  ∷ x6 eta ∷ x7 eta ∷ x8 eta ∷ x9 eta ∷ [])

dotScaleLeft : ∀ scalar normal point →
  dot (vectorScale scalar normal) point
  ≡ scalar * dot normal point
dotScaleLeft scalar normal point = solve
  ( scalar
  ∷ x1 normal ∷ x2 normal ∷ x3 normal ∷ x4 normal ∷ x5 normal
  ∷ x6 normal ∷ x7 normal ∷ x8 normal ∷ x9 normal
  ∷ x1 point ∷ x2 point ∷ x3 point ∷ x4 point ∷ x5 point
  ∷ x6 point ∷ x7 point ∷ x8 point ∷ x9 point ∷ [])

dotAddLeft : ∀ left right point →
  dot (vectorAdd left right) point
  ≡ dot left point + dot right point
dotAddLeft left right point = solve
  ( x1 left ∷ x2 left ∷ x3 left ∷ x4 left ∷ x5 left
  ∷ x6 left ∷ x7 left ∷ x8 left ∷ x9 left
  ∷ x1 right ∷ x2 right ∷ x3 right ∷ x4 right ∷ x5 right
  ∷ x6 right ∷ x7 right ∷ x8 right ∷ x9 right
  ∷ x1 point ∷ x2 point ∷ x3 point ∷ x4 point ∷ x5 point
  ∷ x6 point ∷ x7 point ∷ x8 point ∷ x9 point ∷ [])

record LinearLowerConstraint : Set where
  constructor linear-lower-constraint
  field
    normal : NineVector
    lowerBound : ℚ

open LinearLowerConstraint public

Satisfies : NineVector → LinearLowerConstraint → Set
Satisfies point constraint =
  lowerBound constraint ≤ dot (normal constraint) point

record DualConstraintCell : Set where
  constructor dual-constraint-cell
  field
    constraint : LinearLowerConstraint
    multiplier : ℚ
    multiplierNonnegative : 0ℚ ≤ multiplier

open DualConstraintCell public

data SatisfiesDualCells : NineVector → List DualConstraintCell → Set where
  sat[] : ∀ {point} → SatisfiesDualCells point []
  sat∷ : ∀ {point cell rest} →
    Satisfies point (constraint cell) →
    SatisfiesDualCells point rest →
    SatisfiesDualCells point (cell ∷ rest)

combinedNormal : List DualConstraintCell → NineVector
combinedNormal [] = zeroVector
combinedNormal (cell ∷ rest) =
  vectorAdd
    (vectorScale (multiplier cell) (normal (constraint cell)))
    (combinedNormal rest)

combinedLower : List DualConstraintCell → ℚ
combinedLower [] = 0ℚ
combinedLower (cell ∷ rest) =
  multiplier cell * lowerBound (constraint cell) + combinedLower rest

weightedConstraintBound :
  ∀ point cell →
  Satisfies point (constraint cell) →
  multiplier cell * lowerBound (constraint cell)
  ≤ dot
      (vectorScale (multiplier cell) (normal (constraint cell)))
      point
weightedConstraintBound point cell satisfied =
  let
    instance multiplierNN = nonNegative (multiplierNonnegative cell)
    scaled :
      multiplier cell * lowerBound (constraint cell)
      ≤ multiplier cell * dot (normal (constraint cell)) point
    scaled = ℚP.*-monoˡ-≤-nonNeg (multiplier cell) satisfied
  in
  subst
    (λ upper →
      multiplier cell * lowerBound (constraint cell) ≤ upper)
    (symmetry (dotScaleLeft
      (multiplier cell) (normal (constraint cell)) point))
    scaled
  where
  symmetry : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symmetry refl = refl

combinedConstraintBound :
  ∀ point cells →
  SatisfiesDualCells point cells →
  combinedLower cells ≤ dot (combinedNormal cells) point
combinedConstraintBound point [] sat[] = ℚP.≤-refl
combinedConstraintBound point (cell ∷ rest) (sat∷ current restSat) =
  let
    pairBound = ℚP.+-mono-≤
      (weightedConstraintBound point cell current)
      (combinedConstraintBound point rest restSat)

    rightMeaning :
      dot (vectorScale (multiplier cell) (normal (constraint cell))) point
        + dot (combinedNormal rest) point
      ≡ dot (combinedNormal (cell ∷ rest)) point
    rightMeaning = symmetry
      (dotAddLeft
        (vectorScale (multiplier cell) (normal (constraint cell)))
        (combinedNormal rest)
        point)
  in
  subst
    (λ upper → combinedLower (cell ∷ rest) ≤ upper)
    rightMeaning
    pairBound
  where
  symmetry : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symmetry refl = refl

record NineOwnerDualNoGoCertificate : Set where
  constructor nine-owner-dual-no-go-certificate
  field
    cells : List DualConstraintCell
    normalsCombineToTotal : combinedNormal cells ≡ onesVector
    combinedLowerAtLeastOne : 1ℚ ≤ combinedLower cells

open NineOwnerDualNoGoCertificate public

dualCertificateForcesEtaTotalAtLeastOne :
  (certificate : NineOwnerDualNoGoCertificate) →
  (eta : NineVector) →
  SatisfiesDualCells eta (cells certificate) →
  1ℚ ≤ etaTotal eta
dualCertificateForcesEtaTotalAtLeastOne certificate eta feasible =
  let
    aggregate :
      combinedLower (cells certificate)
      ≤ dot (combinedNormal (cells certificate)) eta
    aggregate = combinedConstraintBound eta (cells certificate) feasible

    oneToDot :
      1ℚ ≤ dot (combinedNormal (cells certificate)) eta
    oneToDot = ℚP.≤-trans
      (combinedLowerAtLeastOne certificate)
      aggregate

    normalMeaning :
      dot (combinedNormal (cells certificate)) eta
      ≡ etaTotal eta
    normalMeaning = trans
      (cong (λ normalVector → dot normalVector eta)
        (normalsCombineToTotal certificate))
      (dotOnesIsEtaTotal eta)
  in
  subst (λ upper → 1ℚ ≤ upper) normalMeaning oneToDot

nineOwnerDualNoGoCertificateTyped : Bool
nineOwnerDualNoGoCertificateTyped = true

physicalNineOwnerDualNoGoCertificateConstructed : Bool
physicalNineOwnerDualNoGoCertificateConstructed = false

nineOwnerDualNoGoCertificateTypedIsTrue :
  nineOwnerDualNoGoCertificateTyped ≡ true
nineOwnerDualNoGoCertificateTypedIsTrue = refl
