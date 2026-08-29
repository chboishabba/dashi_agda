module DASHI.Physics.Closure.NSTriadKNExternalHHEuclideanSquareGapFactorRound125Exact where

------------------------------------------------------------------------
-- ROUND125 / EUCLIDEAN-SQUARE GAP FACTORS THROUGH THE LOW OUTPUT
--
-- Round124 proves the max-norm radial reverse-triangle gain.  For the physical
-- curl eigenvalues, however, the natural radial frequency is Euclidean.  Before
-- introducing any square-root authority, there is a stronger division-free
-- exact identity on the integer lattice:
--
--   |q|_2^2 - |p|_2^2
--     = (p+q) . (q-p)
--     = k . (q-p).
--
-- Thus even at the squared-frequency level the difference carries one literal
-- LOW OUTPUT factor k.  This is the correct HH->low algebraic geometry.  It is
-- complementary to Round124's radial reverse triangle and avoids the misleading
-- interpretation that the large vector separation |q-p| itself is the gain.
--
-- The remaining analytic bridge is ordinary same-helicity square-root
-- factorisation
--
--   |q|-|p| = (|q|^2-|p|^2)/(|q|+|p|),
--
-- together with the already checked three-shell lower bound on the high legs.
-- That bridge is deliberately not postulated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; _-_; _*_; -_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plane

module RingZ = NR IntRS.ring

subtractMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
subtractMode q p = Z3.addMode q (Z3.negateMode p)

squareGap : Z3.FourierMode → Z3.FourierMode → ℤ
squareGap p q = Plane.modeNormSquared q - Plane.modeNormSquared p

sumDifferenceDot : Z3.FourierMode → Z3.FourierMode → ℤ
sumDifferenceDot p q =
  Plane.dotMode (Z3.addMode p q) (subtractMode q p)

squareGapFactorsThroughSum :
  ∀ p q → squareGap p q ≡ sumDifferenceDot p q
squareGapFactorsThroughSum
    (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      ( (qx * qx + qy * qy + qz * qz)
          - (px * px + py * py + pz * pz)
      , (px + qx) * (qx - px)
          + (py + qy) * (qy - py)
          + (pz + qz) * (qz - pz)))
    refl px py pz qx qy qz

resonantSquareGapFactorsThroughOutput :
  (tau : Physical.PhysicalTriadIncidence) →
  squareGap (Physical.p tau) (Physical.q tau)
  ≡ Plane.dotMode
      (Physical.k tau)
      (subtractMode (Physical.q tau) (Physical.p tau))
resonantSquareGapFactorsThroughOutput tau =
  subst
    (λ output →
      squareGap (Physical.p tau) (Physical.q tau)
      ≡ Plane.dotMode output
          (subtractMode (Physical.q tau) (Physical.p tau)))
    (Physical.resonance tau)
    (squareGapFactorsThroughSum (Physical.p tau) (Physical.q tau))

-- The same identity with the orientation reversed.  Keeping both signs explicit
-- makes later absolute-value transport independent of an arbitrary p/q choice.
reverseSquareGapFactorsThroughOutput :
  (tau : Physical.PhysicalTriadIncidence) →
  squareGap (Physical.q tau) (Physical.p tau)
  ≡ Plane.dotMode
      (Physical.k tau)
      (subtractMode (Physical.p tau) (Physical.q tau))
reverseSquareGapFactorsThroughOutput tau =
  subst
    (λ output →
      squareGap (Physical.q tau) (Physical.p tau)
      ≡ Plane.dotMode output
          (subtractMode (Physical.p tau) (Physical.q tau)))
    (Physical.resonance tau)
    (reverseForSum (Physical.p tau) (Physical.q tau))
  where
  reverseForSum : ∀ p q →
    squareGap q p
    ≡ Plane.dotMode (Z3.addMode p q) (subtractMode p q)
  reverseForSum (Z3.mode px py pz) (Z3.mode qx qy qz) =
    RingZ.solve 6
      (λ px py pz qx qy qz →
        ( (px * px + py * py + pz * pz)
            - (qx * qx + qy * qy + qz * qz)
        , (px + qx) * (px - qx)
            + (py + qy) * (py - qy)
            + (pz + qz) * (pz - qz)))
      refl px py pz qx qy qz

round125EuclideanSquareGapFactorizationClosed : Bool
round125EuclideanSquareGapFactorizationClosed = true

round125LowOutputFactorIsLiteral : Bool
round125LowOutputFactorIsLiteral = true

round125SameHelicitySquareRootQuotientBridgeClosed : Bool
round125SameHelicitySquareRootQuotientBridgeClosed = false

round125HHCriticalSignedClassPaymentClosed : Bool
round125HHCriticalSignedClassPaymentClosed = false

round125EuclideanSquareGapFactorizationClosedIsTrue :
  round125EuclideanSquareGapFactorizationClosed ≡ true
round125EuclideanSquareGapFactorizationClosedIsTrue = refl

round125LowOutputFactorIsLiteralIsTrue :
  round125LowOutputFactorIsLiteral ≡ true
round125LowOutputFactorIsLiteralIsTrue = refl

round125SameHelicitySquareRootQuotientBridgeClosedIsFalse :
  round125SameHelicitySquareRootQuotientBridgeClosed ≡ false
round125SameHelicitySquareRootQuotientBridgeClosedIsFalse = refl

round125HHCriticalSignedClassPaymentClosedIsFalse :
  round125HHCriticalSignedClassPaymentClosed ≡ false
round125HHCriticalSignedClassPaymentClosedIsFalse = refl
