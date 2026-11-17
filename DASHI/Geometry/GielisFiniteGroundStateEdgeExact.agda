{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisFiniteGroundStateEdgeExact where

------------------------------------------------------------------------
-- GIELIS FINITE DISCRETE SPECTRAL CERTIFICATE: NATIVE RATIONAL CORE
--
-- A symmetric nonnegative edge-weight graph has the exact ground-state
-- identity (write x_i=q_i*u_i):
--
--   sum_edges (q_i q_j (u_i-u_j)^2)
--    + sum_edges (2q_i q_j u_i u_j)
--    = sum_edges (q_i q_j (u_i^2+u_j^2)).
--
-- The proof uses the ORIGINAL rational ring solver, finite sums,
-- and native nonnegative-square owners.  No generic new Perron library,
-- no floating eigenvalue and no Collatz/Syracuse iteration.
--
-- The original Gielis raster 4I-B operator is handled by grouping the
-- retained edges with its vertex potential. This module proves the
-- all-finite-edge-list identity and nonnegative edge correction.
-- THE FULL RASTER VERTEX-DIAGONAL ASSEMBLY AND CONTINUUM LIMIT remain
-- separate concrete instantiation/analytic obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

record WeightedGroundStateEdge : Set where
  constructor weighted-edge
  field
    qLeft qRight : ℚ
    uLeft uRight : ℚ
    weightNonnegative : 0ℚ ≤ qLeft * qRight

open WeightedGroundStateEdge public

edgeWeight : WeightedGroundStateEdge → ℚ
edgeWeight e = qLeft e * qRight e

edgeSquare : WeightedGroundStateEdge → ℚ
edgeSquare e =
  edgeWeight e * ((uLeft e - uRight e) * (uLeft e - uRight e))

edgeCross : WeightedGroundStateEdge → ℚ
edgeCross e =
  (edgeWeight e * (uLeft e * uRight e))
  + (edgeWeight e * (uLeft e * uRight e))

edgeDiagonal : WeightedGroundStateEdge → ℚ
edgeDiagonal e =
  (edgeWeight e * (uLeft e * uLeft e))
  + (edgeWeight e * (uRight e * uRight e))

-- The polynomial identity is universal in the four rational coordinates.
edgeGroundStateIdentity :
  ∀ e → edgeSquare e + edgeCross e ≡ edgeDiagonal e
edgeGroundStateIdentity (weighted-edge a b x y _) =
  Ring.solve-∀ a b x y

-- The correction is nonnegative for the chosen edge-weight proof.
edgeSquareNonnegative :
  ∀ e → 0ℚ ≤ edgeSquare e
edgeSquareNonnegative e =
  subst
    (λ lower → lower ≤ edgeSquare e)
    (ℚP.*-zeroʳ (edgeWeight e))
    (Norm.scaleNonnegative
      (edgeWeight e)
      (weightNonnegative e)
      (FiniteL2.squareNonnegative (uLeft e - uRight e)))

finiteEdgeSquareSumNonnegative :
  ∀ edges →
  0ℚ ≤ Sums.sumRational edges edgeSquare
finiteEdgeSquareSumNonnegative [] = ℚP.≤-refl
finiteEdgeSquareSumNonnegative (e ∷ es) =
  FiniteL2.addNonnegative
    (edgeSquareNonnegative e)
    (finiteEdgeSquareSumNonnegative es)

finiteGroundStateEdgeIdentity :
  ∀ edges →
  Sums.sumRational edges edgeSquare
    + Sums.sumRational edges edgeCross
  ≡ Sums.sumRational edges edgeDiagonal
finiteGroundStateEdgeIdentity edges =
  trans
    (sym (Fubini.sumRationalAdd edges edgeSquare edgeCross))
    (Sums.sumRationalCong
      edges
      (λ e → edgeSquare e + edgeCross e)
      edgeDiagonal
      edgeGroundStateIdentity)

-- The new general finite identity and nonnegative correction are NOT a
-- claim that a selected physical finite-difference grid equals the
-- continuum Dirichlet operator. That remains the original G12 frontier.
