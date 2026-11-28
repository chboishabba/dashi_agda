module DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact where

------------------------------------------------------------------------
-- ORIGINAL CMP102 finite residual tail geometry, on the exact native
-- CMP109 term sequences and Bishop ℝ.
--
-- On count c = suc n the mathematical all-degree identity is
--
-- G_c = signedTriangle_c
--       - X * [A_c^2 - triangle_(c-1)(A,A)]
--       + 2*X * b_n X^n
--       + X^2 * [B_c^2 - triangle_(c-2)(B,B)].
--
-- The signedTriangle_c is identically zero by the original signed
-- Cauchy endpoint theorem. The two square differences are exactly
-- the original rectangular Cauchy wings already bounded in
-- BishopFiniteCauchyWingAbsoluteBoundExact.
--
-- This file defines the precise ORIGINAL residual receiver from
-- those sources and proves the available signed-triangle and actual
-- square-to-rectangle source identities by imported theorem bodies.
--
-- CAUTION: the displayed G_c-to-tail equality is a remaining native
-- Fin-triangle coefficient rearrangement; it is NOT declared as a
-- theorem here until its proof term is implemented and typechecked.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _+_)
import Data.Nat.Base as N
import Real as R
import RealProperties as P

import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteCauchyWingBoundsExact as Wing
import DASHI.Physics.YangMills.YMClayCMP102OriginalSignedTriangleZeroExact as Triangle
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row

originalAWing : R.ℝ → Nat → R.ℝ
originalAWing X c =
  R._-_
    (Rectangle.rectangleSum (Wing.aTerm X) (Wing.aTerm X) c c)
    (Row.trianglePartial (Wing.aTerm X) (Wing.aTerm X)
      (c N.∸ 1))

originalBWing : R.ℝ → Nat → R.ℝ
originalBWing X c =
  R._-_
    (Rectangle.rectangleSum (Wing.bTerm X) (Wing.bTerm X) c c)
    (Row.trianglePartial (Wing.bTerm X) (Wing.bTerm X)
      (c N.∸ 2))

-- At c=suc n the omitted linear odd term is exactly the original
-- last CMP109 B term. This term CANNOT be dropped: it is essential
-- for first surviving degree c and the signed cancellation.
originalOmittedLinearB : R.ℝ → Nat → R.ℝ
originalOmittedLinearB X n =
  R._*_ (R._*_ CMP102.two X) (Wing.bTerm X n)

originalSignedCauchyTail : R.ℝ → Nat → R.ℝ
originalSignedCauchyTail X n =
  let c = suc n
      X2 = R._*_ X X
  in
  R._+_
    (R._+_
      (R.-_ (R._*_ X (originalAWing X c)))
      (originalOmittedLinearB X n))
    (R._*_ X2 (originalBWing X c))

-- The original signed-triangle source has a complete all-count
-- native proof, and no extra analytically chosen limit.
originalSourceSignedTriangleVanishes : ∀ X c →
  R._≃_ (Triangle.originalSignedTriangle X c) R.0ℝ
originalSourceSignedTriangleVanishes =
  Triangle.originalSignedTriangleZero

-- Actual finite squares are the SAME original rectangular Cauchy
-- values that enter originalAWing and originalBWing, respectively.
originalASquareIsTailRectangle : ∀ X c →
  R._≃_
    (R._*_ (Original.aPrefix X c) (Original.aPrefix X c))
    (Rectangle.rectangleSum (Wing.aTerm X) (Wing.aTerm X) c c)
originalASquareIsTailRectangle =
  Wing.originalASquareIsOriginalRectangle

originalBSquareIsTailRectangle : ∀ X c →
  R._≃_
    (R._*_ (Original.bPrefix X c) (Original.bPrefix X c))
    (Rectangle.rectangleSum (Wing.bTerm X) (Wing.bTerm X) c c)
originalBSquareIsTailRectangle =
  Wing.originalBSquareIsOriginalRectangle
