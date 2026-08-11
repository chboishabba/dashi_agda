module DASHI.Physics.Closure.NSTriadKNVorticityLineOrthogonalResidualRound38Exact where

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
-- Make the P_v/Q_v reading of the Round-37 stretching bound exact without
-- defining the division by |v|^2.  An orthogonal line decomposition supplies
-- a detail vector d and scalar alpha with
--
--   source = d + alpha target,
--   target . d = 0.
--
-- The line receipt is unchanged by the parallel component, and Lagrange's
-- identity gives the exact division-free relation
--
--   |source x target|^2 = |target|^2 |d|^2.
--
-- Combining this with the already checked corrected-strain estimate yields
--
--   |target . S_theta(source) target|^2
--     <= |target|^4 |d|^2
--
-- for unit theta.  Thus the source component parallel to the target line is
-- not merely small: it is exactly invisible to stretching.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNVorticityLineResidualRound38Exact as Residual
import DASHI.Physics.Closure.NSTriadKNVortexStretchingGeometricFactorRound37Exact as Stretch
import DASHI.Physics.Closure.NSTriadKNVortexStretchingDirectionalBoundRound37Exact as Bound

record OrthogonalLineDecomposition
    (target source : V.Vector3) : Set where
  constructor orthogonal-line-decomposition
  field
    detail : V.Vector3
    parallelCoefficient : ℚ
    sourceMeaning :
      source ≡ Residual.parallelShift parallelCoefficient target detail
    detailTransverse : V.dot target detail ≡ 0ℚ

open OrthogonalLineDecomposition public

lineResidualEqualsDetailCrossTarget :
  ∀ {target source} →
  (decomposition : OrthogonalLineDecomposition target source) →
  Residual.lineResidual target source
  ≡ BS.cross (detail decomposition) target
lineResidualEqualsDetailCrossTarget {target} {source} decomposition =
  trans
    (cong (Residual.lineResidual target) (sourceMeaning decomposition))
    (Residual.lineResidualIgnoresParallelComponent
      (parallelCoefficient decomposition)
      target
      (detail decomposition))

lineResidualNormSquaredExact :
  ∀ {target source} →
  (decomposition : OrthogonalLineDecomposition target source) →
  V.normSquared (Residual.lineResidual target source)
  ≡ V.normSquared target * V.normSquared (detail decomposition)
lineResidualNormSquaredExact {target} {source} decomposition =
  trans
    (cong V.normSquared
      (lineResidualEqualsDetailCrossTarget decomposition))
    (trans
      (BS.crossNormLagrange (detail decomposition) target)
      (trans
        (cong
          (λ pairing →
            V.normSquared (detail decomposition) * V.normSquared target
              - pairing * pairing)
          detailDotTargetZero)
        (solve
          ( V.normSquared target
          ∷ V.normSquared (detail decomposition)
          ∷ []))))
  where
  detailDotTargetZero :
    V.dot (detail decomposition) target ≡ 0ℚ
  detailDotTargetZero =
    trans
      (V.dotCommutative (detail decomposition) target)
      (detailTransverse decomposition)

stretchingSquareControlledByLineDetail :
  ∀ theta {source target} →
  V.normSquared theta ≡ 1ℚ →
  (decomposition : OrthogonalLineDecomposition target source) →
  L2.square (Stretch.stretchingScalar theta source target)
  ≤
  V.normSquared target
    * (V.normSquared target * V.normSquared (detail decomposition))
stretchingSquareControlledByLineDetail theta {source} {target}
    thetaUnit decomposition =
  let
    raw = Bound.stretchingSquareControlledByCrossMisalignment
      theta source target thetaUnit
  in
  subst
    (λ residualNorm →
      L2.square (Stretch.stretchingScalar theta source target)
      ≤ V.normSquared target * residualNorm)
    (lineResidualNormSquaredExact decomposition)
    raw

vorticityLineOrthogonalResidualBoundClosed : Bool
vorticityLineOrthogonalResidualBoundClosed = true

vorticityLineOrthogonalResidualBoundClosedIsTrue :
  vorticityLineOrthogonalResidualBoundClosed ≡ true
vorticityLineOrthogonalResidualBoundClosedIsTrue = refl
