module DASHI.Physics.Closure.NSTriadKNPhysicalResonantEuclideanSquareTriangleRound218Exact where

------------------------------------------------------------------------
-- ROUND218 / LITERAL RESONANCE -> EUCLIDEAN SQUARE TRIANGLE
--
-- Round217 consumes the radical-free physical inequality
--
--   |k|^2 <= 2 (|p|^2 + |q|^2)
--
-- on a resonant Fourier incidence p+q=k.  This module proves that premise
-- directly on the exact rational lattice carrier.  Coordinatewise,
--
--   2(a^2+b^2) - (a+b)^2 = (a-b)^2 >= 0.
--
-- Summing the three coordinate defects gives the desired three-dimensional
-- inequality.  No norm square-root or analytic triangle theorem is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

addModeSquareTriangle :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (p q : Z3.FourierMode) →
  C3.normSquared I (Z3.addMode p q)
  ≤ two * (C3.normSquared I p + C3.normSquared I q)
addModeSquareTriangle E I
    (Z3.mode px py pz) (Z3.mode qx qy qz) =
  let
    ax = C3.embedInteger E px
    ay = C3.embedInteger E py
    az = C3.embedInteger E pz
    bx = C3.embedInteger E qx
    by = C3.embedInteger E qy
    bz = C3.embedInteger E qz

    dx = Rational.square (ax - bx)
    dy = Rational.square (ay - by)
    dz = Rational.square (az - bz)

    defectNN : 0ℚ ≤ dx + dy + dz
    defectNN =
      Rational.addNonnegative
        (Rational.addNonnegative
          (Rational.squareNonnegative (ax - bx))
          (Rational.squareNonnegative (ay - by)))
        (Rational.squareNonnegative (az - bz))

    p2 = C3.normSquared I (Z3.mode px py pz)
    q2 = C3.normSquared I (Z3.mode qx qy qz)
    k2 = C3.normSquared I (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz))

    raised : k2 ≤ k2 + (dx + dy + dz)
    raised =
      subst
        (λ lower → lower ≤ k2 + (dx + dy + dz))
        (ℚP.+-identityʳ k2)
        (ℚP.+-monoʳ-≤ k2 defectNN)

    endpoint :
      k2 + (dx + dy + dz)
      ≡ two * (p2 + q2)
    endpoint
      rewrite C3.normSquaredMeaning I (Z3.mode px py pz)
            | C3.normSquaredMeaning I (Z3.mode qx qy qz)
            | C3.normSquaredMeaning I
                (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz))
            | C3.embedAdd E px qx
            | C3.embedAdd E py qy
            | C3.embedAdd E pz qz =
      solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])
  in
  subst (λ upper → k2 ≤ upper) endpoint raised

resonantEuclideanSquareTriangle :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  {p q k : Z3.FourierMode} →
  Z3.Resonance p q k →
  C3.normSquared I k
  ≤ two * (C3.normSquared I p + C3.normSquared I q)
resonantEuclideanSquareTriangle E I {p} {q} {k} resonance =
  subst
    (λ selected →
      C3.normSquared I selected
      ≤ two * (C3.normSquared I p + C3.normSquared I q))
    (Z3.Resonance.closes resonance)
    (addModeSquareTriangle E I p q)

round218PhysicalResonantEuclideanSquareTriangleClosed : Bool
round218PhysicalResonantEuclideanSquareTriangleClosed = true

round218UsesSquareRootTriangle : Bool
round218UsesSquareRootTriangle = false

round218PackageAClosed : Bool
round218PackageAClosed = false

round218ClayPromotion : Bool
round218ClayPromotion = false

round218PhysicalResonantEuclideanSquareTriangleClosedIsTrue :
  round218PhysicalResonantEuclideanSquareTriangleClosed ≡ true
round218PhysicalResonantEuclideanSquareTriangleClosedIsTrue = refl

round218PackageAClosedIsFalse : round218PackageAClosed ≡ false
round218PackageAClosedIsFalse = refl

round218ClayPromotionIsFalse : round218ClayPromotion ≡ false
round218ClayPromotionIsFalse = refl
