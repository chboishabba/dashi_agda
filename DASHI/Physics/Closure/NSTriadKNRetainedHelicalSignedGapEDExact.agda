module DASHI.Physics.Closure.NSTriadKNRetainedHelicalSignedGapEDExact where

------------------------------------------------------------------------
-- RETAINED PHYSICAL MODE RADII -> FOUR-HELICITY SIGNED GAP ED BOUND
--
-- The canonical finite NS system retains only nonzero Fourier modes.  On the
-- physical rational carrier we also have:
--
--   1 <= |k|^2,
--   modeNorm(k)^2 = |k|^2,
--   0 <= modeNorm(k).
--
-- Hence every retained radius r satisfies r <= r^2.  No square root is used:
-- if r <= 1 then r <= 1 <= r^2; if 1 <= r then nonnegative scaling gives
-- r = r*1 <= r*r.
--
-- It follows by four finite helicity cases that
--
--   lambda_q^t - lambda_p^s <= r_p^2 + r_q^2.
--
-- This is precisely the signed-gap hypothesis consumed by the sign-robust
-- self-phase ED kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; NonNegative; nonNegative; _+_; _*_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact as R464
import DASHI.Physics.Closure.NSTriadKNPhysicalHHAndNestedRadiusCompilerRound468Exact as R468

F : C3.RealField _
F = Rational.rationalRealField

radiusBelowSquareFromUnitGap :
  (r square : ℚ) →
  0ℚ ≤ r →
  1ℚ ≤ square →
  r * r ≡ square →
  r ≤ square
radiusBelowSquareFromUnitGap r square rNN unitGap squareMeaning
  with ℚP.≤-total r 1ℚ
... | inj₁ r≤one =
  ℚP.≤-trans r≤one unitGap
... | inj₂ one≤r =
  let
    instance rNNI : NonNegative r
    rNNI = nonNegative rNN

    scaled : r * 1ℚ ≤ r * r
    scaled = ℚP.*-monoˡ-≤-nonNeg r one≤r

    r≤rr : r ≤ r * r
    r≤rr =
      subst
        (_≤ r * r)
        (ℚP.*-identityʳ r)
        scaled
  in
  subst
    (r ≤_)
    squareMeaning
    r≤rr

module PhysicalRetainedGap
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (radiusCalibration :
      R464.PhysicalSquareAndMHDCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        S)
    (orientation : R468.PhysicalRadiusOrientation S) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem

  radius : Z3.FourierMode → ℚ
  radius mode = Helical.modeNorm S mode

  squareRadius : Z3.FourierMode → ℚ
  squareRadius mode = C3.normSquared I mode

  radiusNN :
    (mode : Z3.FourierMode) →
    0ℚ ≤ radius mode
  radiusNN mode = R468.modeNormNonnegative orientation mode

  nonzeroRadiusBelowSquare :
    (mode : Z3.FourierMode) →
    Z3.NonZeroMode mode →
    radius mode ≤ squareRadius mode
  nonzeroRadiusBelowSquare mode nonzero =
    radiusBelowSquareFromUnitGap
      (radius mode)
      (squareRadius mode)
      (radiusNN mode)
      (R450.nonzeroModeSquareAtLeastOne unitGap mode nonzero)
      (R464.modeNormSquareMeaning
        (R464.squareCalibration radiusCalibration mode))

  retainedRadiusBelowSquare :
    (mode : Z3.FourierMode) →
    (member : mode Cube.∈ Audit.modes system) →
    radius mode ≤ squareRadius mode
  retainedRadiusBelowSquare mode member =
    nonzeroRadiusBelowSquare mode
      (Field30.retainedModeNonzero physicalSystem mode member)

  squareNN :
    (mode : Z3.FourierMode) →
    0ℚ ≤ squareRadius mode
  squareNN mode =
    let
      r = radius mode
      rrNN = Rational.squareNonnegative r
    in
    subst
      (0ℚ ≤_)
      (R464.modeNormSquareMeaning
        (R464.squareCalibration radiusCalibration mode))
      rrNN

  plusPlusGapBelowSquares :
    (p q : Z3.FourierMode) →
    (pMember : p Cube.∈ Audit.modes system) →
    (qMember : q Cube.∈ Audit.modes system) →
    radius q - radius p ≤ squareRadius p + squareRadius q
  plusPlusGapBelowSquares p q pMember qMember =
    let
      q≤q2 = retainedRadiusBelowSquare q qMember
      pNN = radiusNN p
      p2NN = squareNN p

      negP≤zero : - radius p ≤ 0ℚ
      negP≤zero = ℚP.neg-mono-≤ pNN

      addNeg :
        radius q + (- radius p) ≤ radius q + 0ℚ
      addNeg = ℚP.+-mono-≤ ℚP.≤-refl negP≤zero

      gap≤q : radius q - radius p ≤ radius q
      gap≤q =
        let
          leftMeaning :
            radius q - radius p ≡ radius q + (- radius p)
          leftMeaning = solve (radius p ∷ radius q ∷ [])
          rightMeaning : radius q + 0ℚ ≡ radius q
          rightMeaning = ℚP.+-identityʳ (radius q)
        in
        subst
          (_≤ radius q)
          (sym leftMeaning)
          (subst
            (radius q + (- radius p) ≤_)
            rightMeaning
            addNeg)

      q2≤sum : squareRadius q ≤ squareRadius p + squareRadius q
      q2≤sum =
        let
          add : 0ℚ + squareRadius q
            ≤ squareRadius p + squareRadius q
          add = ℚP.+-mono-≤ p2NN ℚP.≤-refl
        in
        subst
          (_≤ squareRadius p + squareRadius q)
          (ℚP.+-identityˡ (squareRadius q))
          add
    in
    ℚP.≤-trans gap≤q (ℚP.≤-trans q≤q2 q2≤sum)

  minusMinusGapBelowSquares :
    (p q : Z3.FourierMode) →
    (pMember : p Cube.∈ Audit.modes system) →
    (qMember : q Cube.∈ Audit.modes system) →
    (- radius q) - (- radius p) ≤ squareRadius p + squareRadius q
  minusMinusGapBelowSquares p q pMember qMember =
    let
      p≤p2 = retainedRadiusBelowSquare p pMember
      qNN = radiusNN q

      negQ≤zero : - radius q ≤ 0ℚ
      negQ≤zero = ℚP.neg-mono-≤ qNN

      add :
        (- radius q) + radius p ≤ 0ℚ + radius p
      add = ℚP.+-mono-≤ negQ≤zero ℚP.≤-refl

      gap≤p : (- radius q) - (- radius p) ≤ radius p
      gap≤p =
        let
          leftMeaning :
            (- radius q) - (- radius p)
            ≡ (- radius q) + radius p
          leftMeaning = solve (radius p ∷ radius q ∷ [])
          rightMeaning : 0ℚ + radius p ≡ radius p
          rightMeaning = ℚP.+-identityˡ (radius p)
        in
        subst
          (_≤ radius p)
          (sym leftMeaning)
          (subst
            ((- radius q) + radius p ≤_)
            rightMeaning
            add)

      p2≤sum : squareRadius p ≤ squareRadius p + squareRadius q
      p2≤sum =
        let
          add2 : squareRadius p + 0ℚ
            ≤ squareRadius p + squareRadius q
          add2 = ℚP.+-mono-≤ ℚP.≤-refl (squareNN q)
        in
        subst
          (_≤ squareRadius p + squareRadius q)
          (ℚP.+-identityʳ (squareRadius p))
          add2
    in
    ℚP.≤-trans gap≤p (ℚP.≤-trans p≤p2 p2≤sum)

  plusMinusGapBelowSquares :
    (p q : Z3.FourierMode) →
    (- radius q) - radius p ≤ squareRadius p + squareRadius q
  plusMinusGapBelowSquares p q =
    let
      negQ≤zero : - radius q ≤ 0ℚ
      negQ≤zero = ℚP.neg-mono-≤ (radiusNN q)
      negP≤zero : - radius p ≤ 0ℚ
      negP≤zero = ℚP.neg-mono-≤ (radiusNN p)

      add :
        (- radius q) + (- radius p) ≤ 0ℚ + 0ℚ
      add = ℚP.+-mono-≤ negQ≤zero negP≤zero

      left≤zero : (- radius q) - radius p ≤ 0ℚ
      left≤zero =
        let
          leftMeaning :
            (- radius q) - radius p
            ≡ (- radius q) + (- radius p)
          leftMeaning = solve (radius p ∷ radius q ∷ [])
          rightMeaning : 0ℚ + 0ℚ ≡ 0ℚ
          rightMeaning = ℚP.+-identityˡ 0ℚ
        in
        subst
          (_≤ 0ℚ)
          (sym leftMeaning)
          (subst
            ((- radius q) + (- radius p) ≤_)
            rightMeaning
            add)

      sumNN : 0ℚ ≤ squareRadius p + squareRadius q
      sumNN = ℚP.+-mono-≤ (squareNN p) (squareNN q)
    in
    ℚP.≤-trans left≤zero sumNN

  minusPlusGapBelowSquares :
    (p q : Z3.FourierMode) →
    (pMember : p Cube.∈ Audit.modes system) →
    (qMember : q Cube.∈ Audit.modes system) →
    radius q - (- radius p) ≤ squareRadius p + squareRadius q
  minusPlusGapBelowSquares p q pMember qMember =
    let
      p≤p2 = retainedRadiusBelowSquare p pMember
      q≤q2 = retainedRadiusBelowSquare q qMember

      summed :
        radius q + radius p ≤ squareRadius q + squareRadius p
      summed = ℚP.+-mono-≤ q≤q2 p≤p2

      reordered :
        radius q + radius p ≤ squareRadius p + squareRadius q
      reordered =
        subst
          (radius q + radius p ≤_)
          (ℚP.+-comm (squareRadius q) (squareRadius p))
          summed

      leftMeaning :
        radius q - (- radius p) ≡ radius q + radius p
      leftMeaning = solve (radius p ∷ radius q ∷ [])
    in
    subst
      (_≤ squareRadius p + squareRadius q)
      (sym leftMeaning)
      reordered

  caseSign : Helical.HelicitySign → ℚ → ℚ
  caseSign Helical.plus r = r
  caseSign Helical.minus r = - r

  signedGapBelowSquares :
    (signP signQ : Helical.HelicitySign) →
    (p q : Z3.FourierMode) →
    (pMember : p Cube.∈ Audit.modes system) →
    (qMember : q Cube.∈ Audit.modes system) →
    let signedP =
          caseSign signP (radius p)
        signedQ =
          caseSign signQ (radius q)
    in signedQ - signedP ≤ squareRadius p + squareRadius q
  signedGapBelowSquares Helical.plus Helical.plus p q pMember qMember =
    plusPlusGapBelowSquares p q pMember qMember
  signedGapBelowSquares Helical.plus Helical.minus p q pMember qMember =
    plusMinusGapBelowSquares p q
  signedGapBelowSquares Helical.minus Helical.plus p q pMember qMember =
    minusPlusGapBelowSquares p q pMember qMember
  signedGapBelowSquares Helical.minus Helical.minus p q pMember qMember =
    minusMinusGapBelowSquares p q pMember qMember

  plusPlusGapBelowSquaresNonzero :
    (p q : Z3.FourierMode) →
    Z3.NonZeroMode p →
    Z3.NonZeroMode q →
    radius q - radius p ≤ squareRadius p + squareRadius q
  plusPlusGapBelowSquaresNonzero p q pNZ qNZ =
    let
      q≤q2 = nonzeroRadiusBelowSquare q qNZ
      pNN = radiusNN p
      p2NN = squareNN p
      negP≤zero : - radius p ≤ 0ℚ
      negP≤zero = ℚP.neg-mono-≤ pNN
      addNeg :
        radius q + (- radius p) ≤ radius q + 0ℚ
      addNeg = ℚP.+-mono-≤ ℚP.≤-refl negP≤zero
      gap≤q : radius q - radius p ≤ radius q
      gap≤q =
        subst
          (_≤ radius q)
          (sym (solve (radius p ∷ radius q ∷ [])))
          (subst
            (radius q + (- radius p) ≤_)
            (ℚP.+-identityʳ (radius q))
            addNeg)
      q2≤sum : squareRadius q ≤ squareRadius p + squareRadius q
      q2≤sum =
        subst
          (_≤ squareRadius p + squareRadius q)
          (ℚP.+-identityˡ (squareRadius q))
          (ℚP.+-mono-≤ p2NN ℚP.≤-refl)
    in
    ℚP.≤-trans gap≤q (ℚP.≤-trans q≤q2 q2≤sum)

  minusMinusGapBelowSquaresNonzero :
    (p q : Z3.FourierMode) →
    Z3.NonZeroMode p →
    Z3.NonZeroMode q →
    (- radius q) - (- radius p) ≤ squareRadius p + squareRadius q
  minusMinusGapBelowSquaresNonzero p q pNZ qNZ =
    let
      p≤p2 = nonzeroRadiusBelowSquare p pNZ
      qNN = radiusNN q
      negQ≤zero : - radius q ≤ 0ℚ
      negQ≤zero = ℚP.neg-mono-≤ qNN
      add : (- radius q) + radius p ≤ 0ℚ + radius p
      add = ℚP.+-mono-≤ negQ≤zero ℚP.≤-refl
      gap≤p : (- radius q) - (- radius p) ≤ radius p
      gap≤p =
        subst
          (_≤ radius p)
          (sym (solve (radius p ∷ radius q ∷ [])))
          (subst
            ((- radius q) + radius p ≤_)
            (ℚP.+-identityˡ (radius p))
            add)
      p2≤sum : squareRadius p ≤ squareRadius p + squareRadius q
      p2≤sum =
        subst
          (_≤ squareRadius p + squareRadius q)
          (ℚP.+-identityʳ (squareRadius p))
          (ℚP.+-mono-≤ ℚP.≤-refl (squareNN q))
    in
    ℚP.≤-trans gap≤p (ℚP.≤-trans p≤p2 p2≤sum)

  minusPlusGapBelowSquaresNonzero :
    (p q : Z3.FourierMode) →
    Z3.NonZeroMode p →
    Z3.NonZeroMode q →
    radius q - (- radius p) ≤ squareRadius p + squareRadius q
  minusPlusGapBelowSquaresNonzero p q pNZ qNZ =
    let
      p≤p2 = nonzeroRadiusBelowSquare p pNZ
      q≤q2 = nonzeroRadiusBelowSquare q qNZ
      summed :
        radius q + radius p ≤ squareRadius q + squareRadius p
      summed = ℚP.+-mono-≤ q≤q2 p≤p2
      reordered :
        radius q + radius p ≤ squareRadius p + squareRadius q
      reordered =
        subst
          (radius q + radius p ≤_)
          (ℚP.+-comm (squareRadius q) (squareRadius p))
          summed
    in
    subst
      (_≤ squareRadius p + squareRadius q)
      (sym (solve (radius p ∷ radius q ∷ [])))
      reordered

  signedGapBelowSquaresNonzero :
    (signP signQ : Helical.HelicitySign) →
    (p q : Z3.FourierMode) →
    Z3.NonZeroMode p →
    Z3.NonZeroMode q →
    let signedP = caseSign signP (radius p)
        signedQ = caseSign signQ (radius q)
    in signedQ - signedP ≤ squareRadius p + squareRadius q
  signedGapBelowSquaresNonzero Helical.plus Helical.plus p q pNZ qNZ =
    plusPlusGapBelowSquaresNonzero p q pNZ qNZ
  signedGapBelowSquaresNonzero Helical.plus Helical.minus p q pNZ qNZ =
    plusMinusGapBelowSquares p q
  signedGapBelowSquaresNonzero Helical.minus Helical.plus p q pNZ qNZ =
    minusPlusGapBelowSquaresNonzero p q pNZ qNZ
  signedGapBelowSquaresNonzero Helical.minus Helical.minus p q pNZ qNZ =
    minusMinusGapBelowSquaresNonzero p q pNZ qNZ

