module DASHI.Physics.Closure.NSTriadKNVortexStretchingDirectionalBoundRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- DASHI CONTRIBUTION
--
-- Continue the exact Round-37 strain factorization through the first genuine
-- pointwise estimate.  For a unit separation direction theta, source
-- vorticity w and target vorticity v, prove
--
--   | v . S_theta(w) v |^2
--       <= |v|^2 |w x v|^2.
--
-- The proof is finite rational algebra: the preceding exact factorization
-- gives
--
--   v . S_theta(w) v
--     = -(theta.v) theta.(w x v),
--
-- and two Cauchy inequalities follow from the already machine-checked
-- Lagrange identity.  Thus the Constantin--Fefferman directional depletion
-- factor is present in the literal corrected strain action before any
-- singular-kernel integration or shell estimate.
--
-- The remaining A3/A4 frontier is analytic, not this local geometry: insert
-- the literal periodic PV kernel, sum/integrate this pointwise factor with the
-- required shell localization, and retain enough smallness for the owner
-- budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; subst₂; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNVortexStretchingGeometricFactorRound37Exact as Stretch

toGram : V.Vector3 → Gram.Vec3
toGram (V.v3 vx vy vz) = Gram.vec3 vx vy vz

gramDotMeaning : ∀ left right →
  Gram.dot (toGram left) (toGram right) ≡ V.dot left right
gramDotMeaning left right = refl

gramNormMeaning : ∀ value →
  Gram.normSquared (toGram value) ≡ V.normSquared value
gramNormMeaning value = refl

dotSquareCauchy : ∀ left right →
  L2.square (V.dot left right)
  ≤ V.normSquared left * V.normSquared right
dotSquareCauchy left right =
  let
    product = V.normSquared left * V.normSquared right
    squareValue = L2.square (V.dot left right)

    defectNN : 0ℚ ≤ product - squareValue
    defectNN =
      subst
        (0ℚ ≤_)
        defectMeaning
        (Gram.gramDefectNonnegative (toGram left) (toGram right))
      where
      defectMeaning :
        Gram.normSquared (toGram left) * Gram.normSquared (toGram right)
          - L2.square (Gram.dot (toGram left) (toGram right))
        ≡ product - squareValue
      defectMeaning = refl

    shifted :
      squareValue + 0ℚ ≤ squareValue + (product - squareValue)
    shifted = ℚP.+-monoʳ-≤ squareValue defectNN
  in
  subst₂ _≤_
    (solve (squareValue ∷ []))
    (solve (squareValue ∷ product ∷ []))
    shifted

normSquaredVNonnegative : ∀ value → 0ℚ ≤ V.normSquared value
normSquaredVNonnegative (V.v3 vx vy vz) =
  L2.addNonnegative
    (L2.addNonnegative
      (L2.squareNonnegative vx)
      (L2.squareNonnegative vy))
    (L2.squareNonnegative vz)

normProductNonnegative : ∀ left right →
  0ℚ ≤ V.normSquared left * V.normSquared right
normProductNonnegative left right =
  let
    instance
      leftNN = nonNegative (normSquaredVNonnegative left)
      rightNN = nonNegative (normSquaredVNonnegative right)
      productNN =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (V.normSquared left) (V.normSquared right)
  in
  ℚP.nonNegative⁻¹
    (V.normSquared left * V.normSquared right)

stretchingSquareExact : ∀ theta source target →
  L2.square (Stretch.stretchingScalar theta source target)
  ≡
  L2.square (V.dot theta target)
    * L2.square (V.dot theta (BS.cross source target))
stretchingSquareExact theta source target =
  trans
    (cong L2.square
      (Stretch.stretchingScalarMisalignmentFactor theta source target))
    (solve
      ( V.dot theta target
      ∷ V.dot theta (BS.cross source target)
      ∷ []))

stretchingSquareControlledByCrossMisalignment :
  ∀ theta source target →
  V.normSquared theta ≡ 1ℚ →
  L2.square (Stretch.stretchingScalar theta source target)
  ≤ V.normSquared target * V.normSquared (BS.cross source target)
stretchingSquareControlledByCrossMisalignment
    theta source target thetaUnit =
  let
    firstLower = L2.square (V.dot theta target)
    secondLower = L2.square (V.dot theta (BS.cross source target))
    firstUpper = V.normSquared theta * V.normSquared target
    secondUpper =
      V.normSquared theta * V.normSquared (BS.cross source target)

    raw :
      firstLower * secondLower ≤ firstUpper * secondUpper
    raw =
      L2.nonnegativeProductMonotone
        (L2.squareNonnegative (V.dot theta target))
        (L2.squareNonnegative (V.dot theta (BS.cross source target)))
        (normProductNonnegative theta target)
        (normProductNonnegative theta (BS.cross source target))
        (dotSquareCauchy theta target)
        (dotSquareCauchy theta (BS.cross source target))

    upperUnit :
      firstUpper * secondUpper
      ≡ V.normSquared target * V.normSquared (BS.cross source target)
    upperUnit rewrite thetaUnit =
      solve
        ( V.normSquared target
        ∷ V.normSquared (BS.cross source target)
        ∷ [])
  in
  subst₂ _≤_
    (stretchingSquareExact theta source target)
    upperUnit
    raw

parallelVorticityGivesZeroStretchingSquare :
  ∀ theta source target →
  BS.cross source target ≡ V.v3 0ℚ 0ℚ 0ℚ →
  L2.square (Stretch.stretchingScalar theta source target) ≡ 0ℚ
parallelVorticityGivesZeroStretchingSquare theta source target crossZero =
  trans
    (cong L2.square
      (Stretch.parallelCrossZeroKillsStretching
        theta source target crossZero))
    (solve [])

vortexStretchingDirectionalBoundClosed : Bool
vortexStretchingDirectionalBoundClosed = true

periodicPVDirectionalOwnerBoundConstructed : Bool
periodicPVDirectionalOwnerBoundConstructed = false

vortexStretchingDirectionalBoundClosedIsTrue :
  vortexStretchingDirectionalBoundClosed ≡ true
vortexStretchingDirectionalBoundClosedIsTrue = refl

periodicPVDirectionalOwnerBoundConstructedIsFalse :
  periodicPVDirectionalOwnerBoundConstructed ≡ false
periodicPVDirectionalOwnerBoundConstructedIsFalse = refl
