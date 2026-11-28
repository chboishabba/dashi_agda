{-# OPTIONS --safe #-}
module DASHI.Physics.Gravity.KSW668F8QuadraticTidalEntryExact where

-- One ordered matrix-product entry of the synchronous second-order tidal
-- identity. Summation over the intermediate index and continuum geometry
-- are separate. Source-written ring proof, not continuum authority.
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Physics.Gravity.KSW668F8DualElectricWeylReadoutAlgebraExact as W

quarter : ℚ
quarter = W.half * W.half

quadraticEntry :
  (b h ht htt g gt gtt : ℚ) →
  W.half * (h * (b * gt + W.half * gtt)
            + (b * ht + W.half * htt) * g)
    + quarter * (ht * gt)
  ≡ W.half * (b * (ht * g + h * gt))
    + quarter * (htt * g + W.double * (ht * gt) + h * gtt)
    + - (quarter * (ht * gt))
quadraticEntry b h ht htt g gt gtt =
  Ring.solve-∀ b h ht htt g gt gtt
