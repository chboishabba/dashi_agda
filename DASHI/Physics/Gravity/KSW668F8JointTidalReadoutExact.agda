{-# OPTIONS --safe #-}
module DASHI.Physics.Gravity.KSW668F8JointTidalReadoutExact where

-- Consume the existing rational E4/SMS owner on the SAME spatial Laplacian.
-- The original Cartesian/radial Laplacian identification is a separate
-- continuum theorem obligation. This module does not inhabit the physical
-- authority record or assert continuum convergence.
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Physics.Gravity.KSW668F8DualElectricWeylReadoutAlgebraExact as W

tidal : ℚ → ℚ → ℚ → ℚ
tidal scale etaeta eta = - (W.half * (scale * (etaeta + eta)))

jointTidalReadout :
  (scale etaeta eta lap : ℚ) →
  W.readout4 scale etaeta lap
    + W.half * W.readout5 scale etaeta eta lap
  ≡ tidal scale etaeta eta
jointTidalReadout scale etaeta eta lap =
  Ring.solve-∀ scale etaeta eta lap

signedResidual : ℚ → ℚ → ℚ → ℚ
signedResidual scale eta lap = scale * (lap + - eta)

sameLaplacianResidual :
  (scale etaeta eta lap : ℚ) →
  W.readout5 scale etaeta eta lap
  ≡ W.double * W.readout4 scale etaeta lap + signedResidual scale eta lap
sameLaplacianResidual scale etaeta eta lap =
  Ring.solve-∀ scale etaeta eta lap
