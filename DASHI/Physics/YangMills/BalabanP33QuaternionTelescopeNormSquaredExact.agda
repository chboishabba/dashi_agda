module DASHI.Physics.YangMills.BalabanP33QuaternionTelescopeNormSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003. DOI: 10.1201/9781439864180.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Turn the exact four-factor noncommutative telescope into a quantitative,
-- square-root-free rational estimate.  If
--
--   T = A0 A1 A2 A3 - B0 B1 B2 B3,
--
-- then
--
--   N(T) <= 4 [
--       N(A0-B0) N(A1) N(A2) N(A3)
--     + N(B0) N(A1-B1) N(A2) N(A3)
--     + N(B0) N(B1) N(A2-B2) N(A3)
--     + N(B0) N(B1) N(B2) N(A3-B3) ].
--
-- The same upper bound controls the square of the Wilson scalar defect.  This
-- is the exact quantitative bridge from named placement telescopes to the
-- remaining small-field link-factor estimates; no generic norm receipt is
-- accepted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

term0 term1 term2 term3 :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
term0 a0 a1 a2 a3 b0 b1 b2 b3 =
  (Telescope._-q_ a0 b0) Q.*q
    (a1 Q.*q (a2 Q.*q (a3 Q.*q Q.oneQ)))
term1 a0 a1 a2 a3 b0 b1 b2 b3 =
  b0 Q.*q
    ((Telescope._-q_ a1 b1) Q.*q
      (a2 Q.*q (a3 Q.*q Q.oneQ)))
term2 a0 a1 a2 a3 b0 b1 b2 b3 =
  b0 Q.*q
    (b1 Q.*q
      ((Telescope._-q_ a2 b2) Q.*q (a3 Q.*q Q.oneQ)))
term3 a0 a1 a2 a3 b0 b1 b2 b3 =
  b0 Q.*q
    (b1 Q.*q
      (b2 Q.*q ((Telescope._-q_ a3 b3) Q.*q Q.oneQ)))

weightedFactorDefectSum :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion → ℚ
weightedFactorDefectSum a0 a1 a2 a3 b0 b1 b2 b3 =
  Norm.normSq (Telescope._-q_ a0 b0)
    * Norm.normSq a1 * Norm.normSq a2 * Norm.normSq a3
  + Norm.normSq b0
    * Norm.normSq (Telescope._-q_ a1 b1)
    * Norm.normSq a2 * Norm.normSq a3
  + Norm.normSq b0 * Norm.normSq b1
    * Norm.normSq (Telescope._-q_ a2 b2)
    * Norm.normSq a3
  + Norm.normSq b0 * Norm.normSq b1 * Norm.normSq b2
    * Norm.normSq (Telescope._-q_ a3 b3)

oneNormSqExact : Norm.normSq Q.oneQ ≡ + 1 / 1
oneNormSqExact = refl

fourTelescopeTermNormSumExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Norm.normSq (term0 a0 a1 a2 a3 b0 b1 b2 b3)
  + Norm.normSq (term1 a0 a1 a2 a3 b0 b1 b2 b3)
  + Norm.normSq (term2 a0 a1 a2 a3 b0 b1 b2 b3)
  + Norm.normSq (term3 a0 a1 a2 a3 b0 b1 b2 b3)
  ≡ weightedFactorDefectSum a0 a1 a2 a3 b0 b1 b2 b3
fourTelescopeTermNormSumExact a0 a1 a2 a3 b0 b1 b2 b3
  rewrite Norm.normSqMultiplyExact (Telescope._-q_ a0 b0)
      (a1 Q.*q (a2 Q.*q (a3 Q.*q Q.oneQ)))
        | Norm.normSqMultiplyExact a1 (a2 Q.*q (a3 Q.*q Q.oneQ))
        | Norm.normSqMultiplyExact a2 (a3 Q.*q Q.oneQ)
        | Norm.normSqMultiplyExact a3 Q.oneQ
        | Norm.normSqMultiplyExact b0
      ((Telescope._-q_ a1 b1) Q.*q
        (a2 Q.*q (a3 Q.*q Q.oneQ)))
        | Norm.normSqMultiplyExact (Telescope._-q_ a1 b1)
      (a2 Q.*q (a3 Q.*q Q.oneQ))
        | Norm.normSqMultiplyExact b0
      (b1 Q.*q ((Telescope._-q_ a2 b2) Q.*q (a3 Q.*q Q.oneQ)))
        | Norm.normSqMultiplyExact b1
      ((Telescope._-q_ a2 b2) Q.*q (a3 Q.*q Q.oneQ))
        | Norm.normSqMultiplyExact (Telescope._-q_ a2 b2)
      (a3 Q.*q Q.oneQ)
        | Norm.normSqMultiplyExact b0
      (b1 Q.*q (b2 Q.*q ((Telescope._-q_ a3 b3) Q.*q Q.oneQ)))
        | Norm.normSqMultiplyExact b1
      (b2 Q.*q ((Telescope._-q_ a3 b3) Q.*q Q.oneQ))
        | Norm.normSqMultiplyExact b2
      ((Telescope._-q_ a3 b3) Q.*q Q.oneQ)
        | Norm.normSqMultiplyExact (Telescope._-q_ a3 b3) Q.oneQ =
  ℚRing.solve-∀
    (Norm.normSq (Telescope._-q_ a0 b0))
    (Norm.normSq a1) (Norm.normSq a2) (Norm.normSq a3)
    (Norm.normSq b0)
    (Norm.normSq (Telescope._-q_ a1 b1))
    (Norm.normSq b1)
    (Norm.normSq (Telescope._-q_ a2 b2))
    (Norm.normSq b2)
    (Norm.normSq (Telescope._-q_ a3 b3))

fourFactorTelescopeNormSqBound :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Norm.normSq
    (Telescope.fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3)
  ≤ (+ 4 / 1)
      * weightedFactorDefectSum a0 a1 a2 a3 b0 b1 b2 b3
fourFactorTelescopeNormSqBound a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    t0 = term0 a0 a1 a2 a3 b0 b1 b2 b3
    t1 = term1 a0 a1 a2 a3 b0 b1 b2 b3
    t2 = term2 a0 a1 a2 a3 b0 b1 b2 b3
    t3 = term3 a0 a1 a2 a3 b0 b1 b2 b3

    raw :
      Norm.normSq (t0 Q.+q (t1 Q.+q (t2 Q.+q t3)))
      ≤ (+ 4 / 1)
          * (Norm.normSq t0 + Norm.normSq t1
            + Norm.normSq t2 + Norm.normSq t3)
    raw = Norm.normSqSum4Bound t0 t1 t2 t3
  in
  subst
    (λ upper →
      Norm.normSq
        (Telescope.fourFactorTelescope
          a0 a1 a2 a3 b0 b1 b2 b3)
      ≤ upper)
    (cong ((+ 4 / 1) *_)
      (fourTelescopeTermNormSumExact
        a0 a1 a2 a3 b0 b1 b2 b3))
    raw

wilsonScalarDefectSquareBound :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  let defect =
        Telescope.wilsonScalarDifference
          (Telescope.orderedProduct4 a0 a1 a2 a3)
          (Telescope.orderedProduct4 b0 b1 b2 b3)
  in
  defect * defect
  ≤ (+ 4 / 1)
      * weightedFactorDefectSum a0 a1 a2 a3 b0 b1 b2 b3
wilsonScalarDefectSquareBound a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    telescope =
      Telescope.fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3
    defect =
      Telescope.wilsonScalarDifference
        (Telescope.orderedProduct4 a0 a1 a2 a3)
        (Telescope.orderedProduct4 b0 b1 b2 b3)

    scalarExact : defect ≡ - Q.q0 telescope
    scalarExact =
      Telescope.wilsonScalarDifferenceTelescopeExact
        a0 a1 a2 a3 b0 b1 b2 b3

    defectSquareExact :
      defect * defect ≡ Q.q0 telescope * Q.q0 telescope
    defectSquareExact =
      trans
        (cong (λ selected → selected * selected) scalarExact)
        (ℚRing.solve-∀ (Q.q0 telescope))

    scalarSquareBelow :
      defect * defect ≤ Norm.normSq telescope
    scalarSquareBelow =
      subst
        (λ lower → lower ≤ Norm.normSq telescope)
        (sym defectSquareExact)
        (Norm.scalarPartSquareBelowNormSq telescope)

    telescopeBound :
      Norm.normSq telescope
      ≤ (+ 4 / 1)
          * weightedFactorDefectSum a0 a1 a2 a3 b0 b1 b2 b3
    telescopeBound =
      fourFactorTelescopeNormSqBound
        a0 a1 a2 a3 b0 b1 b2 b3
  in
  ℚP.≤-trans scalarSquareBelow telescopeBound

quaternionTelescopeNormSquaredLevel : ProofLevel
quaternionTelescopeNormSquaredLevel = machineChecked

wilsonScalarTelescopeSquareBoundLevel : ProofLevel
wilsonScalarTelescopeSquareBoundLevel = machineChecked
