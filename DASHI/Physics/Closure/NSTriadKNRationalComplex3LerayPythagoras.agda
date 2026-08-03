module DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean Leray; Marco Cannone; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin; DASHI repository contributors.
-- Title: "Literal rational C3 Leray Pythagorean identity and projected-mode
-- contraction".
-- Venue/year: Handbook of Mathematical Fluid Dynamics, Volume 3, 2005;
-- Fourier Analysis and Nonlinear Partial Differential Equations, Springer,
-- 2011; DASHI formal development, 2026.
-- DOI: 10.1016/S1874-5792(05)80006-0;
-- 10.1007/978-3-642-16830-7; the coordinate identity is
-- repository-original and has no DOI.
-- Uses: the literal rank-one projector in NSTriadKNComplex3ExactCarrier, the
-- inverse squared-mode law, rational ring normalization, and nonnegativity of
-- the rank-one correction.
-- Relationship: proves the exact squared identity
--   ||P_k v||^2 = ||v||^2 - |k dot v|^2 / |k|^2
-- on the rational C3 carrier and derives squared Leray contraction. No
-- square-root monotonicity is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation

F : C3.RealField _
F = RationalL2.rationalRealField

square : ℚ → ℚ
square = RationalL2.square

modeNormPolynomial : ℚ → ℚ → ℚ → ℚ
modeNormPolynomial mx my mz = square mx + square my + square mz

valueNormPolynomial : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
valueNormPolynomial xr xi yr yi zr zi =
  square xr + square xi
  + (square yr + square yi)
  + (square zr + square zi)

dotRealPolynomial : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
dotRealPolynomial mx my mz xr yr zr = mx * xr + my * yr + mz * zr

dotImaginaryPolynomial : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
dotImaginaryPolynomial mx my mz xi yi zi = mx * xi + my * yi + mz * zi

dotNormPolynomial :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
dotNormPolynomial mx my mz xr xi yr yi zr zi =
  square (dotRealPolynomial mx my mz xr yr zr)
  + square (dotImaginaryPolynomial mx my mz xi yi zi)

projectedNormPolynomial :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
projectedNormPolynomial mx my mz xr xi yr yi zr zi inverse =
  let
    dr = dotRealPolynomial mx my mz xr yr zr
    di = dotImaginaryPolynomial mx my mz xi yi zi
  in
  square (xr - inverse * dr * mx)
  + square (xi - inverse * di * mx)
  + (square (yr - inverse * dr * my)
    + square (yi - inverse * di * my))
  + (square (zr - inverse * dr * mz)
    + square (zi - inverse * di * mz))

inverseSquaredNormTimesNorm :
  ∀ inverse norm → inverse * norm ≡ 1ℚ →
  (inverse * inverse) * norm ≡ inverse
inverseSquaredNormTimesNorm inverse norm inverseLaw =
  trans (ℚₚ.*-assoc inverse inverse norm)
    (trans (cong (inverse *_) inverseLaw) (ℚₚ.*-identityʳ inverse))

coordinateLerayPythagoras :
  ∀ mx my mz xr xi yr yi zr zi inverse →
  inverse * modeNormPolynomial mx my mz ≡ 1ℚ →
  projectedNormPolynomial mx my mz xr xi yr yi zr zi inverse
  ≡ valueNormPolynomial xr xi yr yi zr zi
    - inverse * dotNormPolynomial mx my mz xr xi yr yi zr zi
coordinateLerayPythagoras
  mx my mz xr xi yr yi zr zi inverse inverseLaw =
  let
    norm = modeNormPolynomial mx my mz
    inverseSquaredNorm : (inverse * inverse) * norm ≡ inverse
    inverseSquaredNorm = inverseSquaredNormTimesNorm inverse norm inverseLaw
    dr = dotRealPolynomial mx my mz xr yr zr
    di = dotImaginaryPolynomial mx my mz xi yi zi
    dotNorm = square dr + square di
    valueNorm = valueNormPolynomial xr xi yr yi zr zi
    expanded :
      projectedNormPolynomial mx my mz xr xi yr yi zr zi inverse
      ≡ valueNorm
        + (((inverse * inverse) * norm) - inverse - inverse) * dotNorm
    expanded = solve
      (mx ∷ my ∷ mz ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ inverse ∷ [])
    reduceInverse :
      valueNorm
      + (((inverse * inverse) * norm) - inverse - inverse) * dotNorm
      ≡ valueNorm + (inverse - inverse - inverse) * dotNorm
    reduceInverse = cong
      (λ coefficient → valueNorm + (coefficient - inverse - inverse) * dotNorm)
      inverseSquaredNorm
  in
  trans expanded (trans reduceInverse (solve (valueNorm ∷ inverse ∷ dotNorm ∷ [])))

rationalLerayCorrection :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → C3.Complex3 F → ℚ
rationalLerayCorrection E I mode value =
  C3.inverseNormSquared I mode
  * L2.complexModulusSquared
      (C3.bilinearDot3 (C3.modeVector E mode) value)

literalValueNormMeaning :
  ∀ xr xi yr yi zr zi →
  L2.complex3NormSquared {F = F}
    (C3.complex3 (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi))
  ≡ valueNormPolynomial xr xi yr yi zr zi
literalValueNormMeaning xr xi yr yi zr zi =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

literalDotNormMeaning :
  ∀ mx my mz xr xi yr yi zr zi →
  L2.complexModulusSquared {F = F}
    (C3.bilinearDot3
      (C3.complex3 (C3.realEmbed F mx) (C3.realEmbed F my) (C3.realEmbed F mz))
      (C3.complex3 (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)))
  ≡ dotNormPolynomial mx my mz xr xi yr yi zr zi
literalDotNormMeaning mx my mz xr xi yr yi zr zi =
  solve (mx ∷ my ∷ mz ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

literalProjectionNormMeaning :
  ∀ (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) xr xi yr yi zr zi →
  L2.complex3NormSquared
    (C3.lerayProject3 E I mode
      (C3.complex3 (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)))
  ≡ projectedNormPolynomial
    (C3.embedInteger E (Z3.kx mode))
    (C3.embedInteger E (Z3.ky mode))
    (C3.embedInteger E (Z3.kz mode))
    xr xi yr yi zr zi (C3.inverseNormSquared I mode)
literalProjectionNormMeaning E I mode xr xi yr yi zr zi = solve
  ( C3.embedInteger E (Z3.kx mode)
  ∷ C3.embedInteger E (Z3.ky mode)
  ∷ C3.embedInteger E (Z3.kz mode)
  ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi
  ∷ C3.inverseNormSquared I mode ∷ [] )

literalRationalC3LerayPythagoreanIdentity :
  ∀ (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) (value : C3.Complex3 F) →
  Z3.NonZeroMode mode →
  L2.complex3NormSquared (C3.lerayProject3 E I mode value)
  ≡ L2.complex3NormSquared value - rationalLerayCorrection E I mode value
literalRationalC3LerayPythagoreanIdentity
  E I mode
  (C3.complex3 (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi))
  nonzero =
  let
    mx = C3.embedInteger E (Z3.kx mode)
    my = C3.embedInteger E (Z3.ky mode)
    mz = C3.embedInteger E (Z3.kz mode)
    inverse = C3.inverseNormSquared I mode
    inverseLaw : inverse * modeNormPolynomial mx my mz ≡ 1ℚ
    inverseLaw = trans
      (sym (cong (inverse *_) (C3.normSquaredMeaning I mode)))
      (C3.inverseLaw I mode nonzero)
    projectionMeaning = literalProjectionNormMeaning E I mode xr xi yr yi zr zi
    coordinateIdentity = coordinateLerayPythagoras
      mx my mz xr xi yr yi zr zi inverse inverseLaw
    valueMeaning = literalValueNormMeaning xr xi yr yi zr zi
    dotMeaning = literalDotNormMeaning mx my mz xr xi yr yi zr zi
    correctionMeaning :
      rationalLerayCorrection E I mode
        (C3.complex3 (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi))
      ≡ inverse * dotNormPolynomial mx my mz xr xi yr yi zr zi
    correctionMeaning = cong (inverse *_) dotMeaning
  in
  trans projectionMeaning
    (trans coordinateIdentity
      (cong₂Subtract (sym valueMeaning) (sym correctionMeaning)))
  where
  cong₂Subtract : ∀ {a b c d : ℚ} → a ≡ b → c ≡ d → a - c ≡ b - d
  cong₂Subtract refl refl = refl

record RationalInverseNormOrder
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set where
  field
    inverseNormSquaredNonnegative :
      ∀ mode → Z3.NonZeroMode mode → 0ℚ ≤ C3.inverseNormSquared I mode

open RationalInverseNormOrder public

rationalLerayCorrectionNonnegative :
  ∀ (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (O : RationalInverseNormOrder E I) mode value →
  (nonzero : Z3.NonZeroMode mode) →
  0ℚ ≤ rationalLerayCorrection E I mode value
rationalLerayCorrectionNonnegative E I O mode value nonzero =
  let
    inverse = C3.inverseNormSquared I mode
    dotValue = C3.bilinearDot3 (C3.modeVector E mode) value
    instance
      inverseNN = nonNegative (inverseNormSquaredNonnegative O mode nonzero)
      dotNN = nonNegative (Separation.complexModulusSquaredNonnegative dotValue)
      productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg inverse
        (L2.complexModulusSquared dotValue)
  in
  ℚₚ.nonNegative⁻¹ (rationalLerayCorrection E I mode value)

rationalLerayNormSquaredContraction :
  ∀ (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (O : RationalInverseNormOrder E I) mode value →
  (nonzero : Z3.NonZeroMode mode) →
  L2.complex3NormSquared (C3.lerayProject3 E I mode value)
  ≤ L2.complex3NormSquared value
rationalLerayNormSquaredContraction E I O mode value nonzero =
  subst
    (λ lower → lower ≤ L2.complex3NormSquared value)
    (sym (literalRationalC3LerayPythagoreanIdentity E I mode value nonzero))
    (RationalL2.subtractNonnegativeBelow
      (L2.complex3NormSquared value)
      (rationalLerayCorrection E I mode value)
      (rationalLerayCorrectionNonnegative E I O mode value nonzero))

rationalProjectedModeNormSquaredBound :
  ∀ (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (O : RationalInverseNormOrder E I) projector differentiated →
  (nonzero : Z3.NonZeroMode projector) →
  L2.complex3NormSquared
    (C3.lerayProject3 E I projector (C3.modeVector E differentiated))
  ≤ L2.complex3NormSquared (C3.modeVector E differentiated)
rationalProjectedModeNormSquaredBound E I O projector differentiated =
  rationalLerayNormSquaredContraction E I O projector (C3.modeVector E differentiated)

literalRationalC3LerayPythagorasClosed : Bool
literalRationalC3LerayPythagorasClosed = true

literalRationalC3LerayPythagorasClosedIsTrue :
  literalRationalC3LerayPythagorasClosed ≡ true
literalRationalC3LerayPythagorasClosedIsTrue = refl

rationalProjectedModeSquaredBoundClosed : Bool
rationalProjectedModeSquaredBoundClosed = true

rationalProjectedModeSquaredBoundClosedIsTrue :
  rationalProjectedModeSquaredBoundClosed ≡ true
rationalProjectedModeSquaredBoundClosedIsTrue = refl
