module DASHI.Physics.Closure.NSTriadKNFiniteGalerkinLocalLipschitzRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Round 26 proved the exact degree-two factorisation
--
--   xy-uv = (x-u)y + u(y-v)
--
-- for every literal rational Galerkin coordinate.  This file supplies the
-- quantitative finite local-Lipschitz majorant.  On a pointwise radius-R ball,
-- and for pointwise difference bounded by delta, each linear atom costs
-- |c| delta and each bilinear atom costs |c|(R+R)delta.  Finite atom lists are
-- summed exactly.  The remaining continuum-real finite-dimensional norm and
-- Picard--Lindelof instance are not claimed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial

AssignmentBound : ℚ → Polynomial.Assignment → Set
AssignmentBound radius state =
  ∀ variable → ∣ state variable ∣ ≤ radius

AssignmentDifferenceBound :
  ℚ → Polynomial.Assignment → Polynomial.Assignment → Set
AssignmentDifferenceBound delta state reference =
  ∀ variable → ∣ state variable - reference variable ∣ ≤ delta

absoluteProductBound :
  ∀ {left right leftBound rightBound : ℚ} →
  ∣ left ∣ ≤ leftBound →
  ∣ right ∣ ≤ rightBound →
  0ℚ ≤ leftBound →
  0ℚ ≤ rightBound →
  ∣ left * right ∣ ≤ leftBound * rightBound
absoluteProductBound
  {left} {right} {leftBound} {rightBound}
  left≤ right≤ leftBoundNN rightBoundNN =
  let
    instance
      absRightNN : NonNegative ∣ right ∣
      absRightNN = ℚₚ.∣-∣-nonNeg right

      leftBoundNonnegative : NonNegative leftBound
      leftBoundNonnegative = nonNegative leftBoundNN

    firstStep :
      ∣ left ∣ * ∣ right ∣ ≤ leftBound * ∣ right ∣
    firstStep =
      ℚₚ.*-monoʳ-≤-nonNeg ∣ right ∣ left≤

    secondStep :
      leftBound * ∣ right ∣ ≤ leftBound * rightBound
    secondStep =
      ℚₚ.*-monoˡ-≤-nonNeg leftBound right≤
  in
  subst
    (λ lower → lower ≤ leftBound * rightBound)
    (sym (ℚₚ.∣p*q∣≡∣p∣*∣q∣ left right))
    (ℚₚ.≤-trans firstStep secondStep)

atomLipschitzWeight :
  ℚ → Polynomial.GalerkinCoordinateAtom → ℚ
atomLipschitzWeight radius
  (Polynomial.viscousLinear output component coefficient) =
  ∣ coefficient ∣
atomLipschitzWeight radius
  (Polynomial.resonantBilinear triad left right coefficient) =
  ∣ coefficient ∣ * (radius + radius)

atomLipschitzWeightNonnegative :
  (radius : ℚ) →
  (atom : Polynomial.GalerkinCoordinateAtom) →
  0ℚ ≤ atomLipschitzWeight radius atom
atomLipschitzWeightNonnegative radius
  (Polynomial.viscousLinear output component coefficient) =
  ℚₚ.0≤∣p∣ coefficient
atomLipschitzWeightNonnegative radius
  (Polynomial.resonantBilinear triad left right coefficient) =
  ℚₚ.nonNegative⁻¹
    (∣ coefficient ∣ * (radius + radius))
  where
  postulate-free-radius-sum : 0ℚ ≤ radius + radius
  postulate-free-radius-sum = ℚₚ.+-mono-≤ ℚₚ.≤-refl ℚₚ.≤-refl

  instance
    coefficientNN : NonNegative ∣ coefficient ∣
    coefficientNN = ℚₚ.∣-∣-nonNeg coefficient

    radiusSumNN : NonNegative (radius + radius)
    radiusSumNN = nonNegative postulate-free-radius-sum

atomDifferenceAbsoluteBound :
  (radius delta : ℚ) →
  0ℚ ≤ radius →
  0ℚ ≤ delta →
  (atom : Polynomial.GalerkinCoordinateAtom) →
  (state reference : Polynomial.Assignment) →
  AssignmentBound radius state →
  AssignmentBound radius reference →
  AssignmentDifferenceBound delta state reference →
  ∣ Polynomial.differenceAtom atom state reference ∣
  ≤ atomLipschitzWeight radius atom * delta
atomDifferenceAbsoluteBound radius delta radiusNN deltaNN
  (Polynomial.viscousLinear output component coefficient)
  state reference stateBound referenceBound differenceBound =
  let
    instance
      coefficientNN : NonNegative ∣ coefficient ∣
      coefficientNN = ℚₚ.∣-∣-nonNeg coefficient

    scaled :
      ∣ coefficient ∣ * ∣ state component - reference component ∣
      ≤ ∣ coefficient ∣ * delta
    scaled =
      ℚₚ.*-monoˡ-≤-nonNeg
        ∣ coefficient ∣
        (differenceBound component)
  in
  subst
    (λ lower → lower ≤ ∣ coefficient ∣ * delta)
    (sym
      (ℚₚ.∣p*q∣≡∣p∣*∣q∣
        coefficient (state component - reference component)))
    scaled
atomDifferenceAbsoluteBound radius delta radiusNN deltaNN
  (Polynomial.resonantBilinear triad left right coefficient)
  state reference stateBound referenceBound differenceBound =
  let
    leftDifference = state left - reference left
    rightDifference = state right - reference right
    firstProduct = leftDifference * state right
    secondProduct = reference left * rightDifference
    inner = firstProduct + secondProduct

    firstProductBound :
      ∣ firstProduct ∣ ≤ delta * radius
    firstProductBound =
      absoluteProductBound
        (differenceBound left)
        (stateBound right)
        deltaNN radiusNN

    secondProductBound :
      ∣ secondProduct ∣ ≤ radius * delta
    secondProductBound =
      absoluteProductBound
        (referenceBound left)
        (differenceBound right)
        radiusNN deltaNN

    innerBound :
      ∣ inner ∣ ≤ delta * radius + radius * delta
    innerBound =
      ℚₚ.≤-trans
        (ℚₚ.∣p+q∣≤∣p∣+∣q∣ firstProduct secondProduct)
        (ℚₚ.+-mono-≤ firstProductBound secondProductBound)

    instance
      coefficientNN : NonNegative ∣ coefficient ∣
      coefficientNN = ℚₚ.∣-∣-nonNeg coefficient

    outerBound :
      ∣ coefficient ∣ * ∣ inner ∣
      ≤ ∣ coefficient ∣ * (delta * radius + radius * delta)
    outerBound =
      ℚₚ.*-monoˡ-≤-nonNeg ∣ coefficient ∣ innerBound

    rightMeaning :
      ∣ coefficient ∣ * (delta * radius + radius * delta)
      ≡ (∣ coefficient ∣ * (radius + radius)) * delta
    rightMeaning =
      solve (∣ coefficient ∣ ∷ radius ∷ delta ∷ [])
  in
  subst
    (λ lower →
      lower ≤ (∣ coefficient ∣ * (radius + radius)) * delta)
    (sym (ℚₚ.∣p*q∣≡∣p∣*∣q∣ coefficient inner))
    (subst
      (λ upper → ∣ coefficient ∣ * ∣ inner ∣ ≤ upper)
      rightMeaning
      outerBound)

atomsLipschitzWeight :
  ℚ → List Polynomial.GalerkinCoordinateAtom → ℚ
atomsLipschitzWeight radius [] = 0ℚ
atomsLipschitzWeight radius (atom ∷ rest) =
  atomLipschitzWeight radius atom
  + atomsLipschitzWeight radius rest

finiteAtomsDifferenceAbsoluteBound :
  (radius delta : ℚ) →
  0ℚ ≤ radius →
  0ℚ ≤ delta →
  (atoms : List Polynomial.GalerkinCoordinateAtom) →
  (state reference : Polynomial.Assignment) →
  AssignmentBound radius state →
  AssignmentBound radius reference →
  AssignmentDifferenceBound delta state reference →
  ∣ Polynomial.differenceAtoms atoms state reference ∣
  ≤ atomsLipschitzWeight radius atoms * delta
finiteAtomsDifferenceAbsoluteBound radius delta radiusNN deltaNN
  [] state reference stateBound referenceBound differenceBound =
  subst
    (λ upper → ∣ 0ℚ ∣ ≤ upper)
    (solve (delta ∷ []))
    (subst
      (λ lower → lower ≤ 0ℚ)
      (sym (ℚₚ.0≤p⇒∣p∣≡p ℚₚ.≤-refl))
      ℚₚ.≤-refl)
finiteAtomsDifferenceAbsoluteBound radius delta radiusNN deltaNN
  (atom ∷ rest) state reference stateBound referenceBound differenceBound =
  let
    atomBound =
      atomDifferenceAbsoluteBound
        radius delta radiusNN deltaNN atom
        state reference stateBound referenceBound differenceBound

    restBound =
      finiteAtomsDifferenceAbsoluteBound
        radius delta radiusNN deltaNN rest
        state reference stateBound referenceBound differenceBound

    summed :
      ∣ Polynomial.differenceAtom atom state reference ∣
        + ∣ Polynomial.differenceAtoms rest state reference ∣
      ≤
      atomLipschitzWeight radius atom * delta
        + atomsLipschitzWeight radius rest * delta
    summed = ℚₚ.+-mono-≤ atomBound restBound

    rightMeaning :
      atomLipschitzWeight radius atom * delta
        + atomsLipschitzWeight radius rest * delta
      ≡ atomsLipschitzWeight radius (atom ∷ rest) * delta
    rightMeaning =
      solve
        ( atomLipschitzWeight radius atom
        ∷ atomsLipschitzWeight radius rest
        ∷ delta
        ∷ [])
  in
  ℚₚ.≤-trans
    (ℚₚ.∣p+q∣≤∣p∣+∣q∣
      (Polynomial.differenceAtom atom state reference)
      (Polynomial.differenceAtoms rest state reference))
    (subst
      (λ upper →
        ∣ Polynomial.differenceAtom atom state reference ∣
          + ∣ Polynomial.differenceAtoms rest state reference ∣
        ≤ upper)
      rightMeaning
      summed)

coordinateRightHandSideLocalLipschitz :
  (radius delta : ℚ) →
  0ℚ ≤ radius →
  0ℚ ≤ delta →
  (equation : Polynomial.LiteralGalerkinCoordinateEquation) →
  (state reference : Polynomial.Assignment) →
  AssignmentBound radius state →
  AssignmentBound radius reference →
  AssignmentDifferenceBound delta state reference →
  ∣ Polynomial.coordinateRightHandSide equation state
      - Polynomial.coordinateRightHandSide equation reference ∣
  ≤ atomsLipschitzWeight radius
      (Polynomial.rightHandSideAtoms equation) * delta
coordinateRightHandSideLocalLipschitz
  radius delta radiusNN deltaNN equation state reference
  stateBound referenceBound differenceBound =
  subst
    (λ lower →
      lower
      ≤ atomsLipschitzWeight radius
          (Polynomial.rightHandSideAtoms equation) * delta)
    (cong ∣_∣
      (Polynomial.coordinateRightHandSideDifference
        equation state reference))
    (finiteAtomsDifferenceAbsoluteBound
      radius delta radiusNN deltaNN
      (Polynomial.rightHandSideAtoms equation)
      state reference stateBound referenceBound differenceBound)

finiteRationalLocalLipschitzMajorantClosed : Bool
finiteRationalLocalLipschitzMajorantClosed = true

continuumRealNormedPicardLindelofInstantiated : Bool
continuumRealNormedPicardLindelofInstantiated = false

finiteRationalLocalLipschitzMajorantClosedIsTrue :
  finiteRationalLocalLipschitzMajorantClosed ≡ true
finiteRationalLocalLipschitzMajorantClosedIsTrue = refl

continuumRealNormedPicardLindelofInstantiatedIsFalse :
  continuumRealNormedPicardLindelofInstantiated ≡ false
continuumRealNormedPicardLindelofInstantiatedIsFalse = refl
