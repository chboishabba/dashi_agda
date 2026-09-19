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

  retainedRadiusBelowSquare :
    (mode : Z3.FourierMode) →
    (member : mode Cube.∈ Audit.modes system) →
    radius mode ≤ squareRadius mode
  retainedRadiusBelowSquare mode member =
    radiusBelowSquareFromUnitGap
      (radius mode)
      (squareRadius mode)
      (radiusNN mode)
      (R450.nonzeroModeSquareAtLeastOne
        unitGap mode
        (Field30.retainedModeNonzero physicalSystem mode member))
      (R464.modeNormSquareMeaning
        (R464.squareCalibration radiusCalibration mode))

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

      gap≤q : radius q - radius p ≤ radius q
      gap≤q =
        let
          negP≤zero : - radius p ≤ 0ℚ
          negP≤zero = ℚP.neg-mono-≤ pNN
          shifted = ℚP.+-mono-≤ ℚP.≤-refl negP≤zero
        in
        subst
          (radius q - radius p ≤_)
          (sym (ℚP.+-identityʳ (radius q)))
          shifted

      q2≤sum : squareRadius q ≤ squareRadius p + squareRadius q
      q2≤sum =
        subst
          (_≤ squareRadius p + squareRadius q)
          (ℚP.+-identityˡ (squareRadius q))
          (ℚP.+-mono-≤ p2NN ℚP.≤-refl)
    in
    ℚP.≤-trans gap≤q (ℚP.≤-trans q≤q2 q2≤sum)

  minusMinusGapBelowSquares :
    (p q : Z3.FourierMode) →
    (pMember : p Cube.∈ Audit.modes system) →
    (qMember : q Cube.∈ Audit.modes system) →
    (- radius q) - (- radius p) ≤ squareRadius p + squareRadius q
  minusMinusGapBelowSquares p q pMember qMember =
    subst
      (_≤ squareRadius p + squareRadius q)
      (solve (radius p ∷ radius q ∷ []))
      (plusPlusGapBelowSquares q p qMember pMember)

  plusMinusGapBelowSquares :
    (p q : Z3.FourierMode) →
    (- radius q) - radius p ≤ squareRadius p + squareRadius q
  plusMinusGapBelowSquares p q =
    let
      pNN = radiusNN p
      qNN = radiusNN q
      negQ≤zero = ℚP.neg-mono-≤ qNN
      negP≤zero = ℚP.neg-mono-≤ pNN
      left≤zero : (- radius q) - radius p ≤ 0ℚ
      left≤zero =
        let
          summed = ℚP.+-mono-≤ negQ≤zero negP≤zero
        in
        subst
          ((- radius q) - radius p ≤_)
          (solve [])
          summed
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
      summed = ℚP.+-mono-≤ q≤q2 p≤p2
    in
    subst
      (_≤ squareRadius p + squareRadius q)
      (solve (radius p ∷ radius q ∷ []))
      (subst
        (λ upper → radius q + radius p ≤ upper)
        (ℚP.+-comm (squareRadius q) (squareRadius p))
        summed)

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

