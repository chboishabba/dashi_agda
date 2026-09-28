{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact where

open import Agda.Builtin.Nat using (Nat; suc)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- RICH BRILLOUIN -> RATIONAL LITERAL GAUSSIAN PROJECTION
--
-- This is the unique surviving Gaussian cross-carrier seam on the preferred
-- S4 path.  It does not choose or alter either normalization.  It states only
-- that the physical rich-shell scalar and the older rational plaquette beta_Z
-- are two representations of the same one-loop localized Gaussian coefficient.
------------------------------------------------------------------------

record RichBrillouinRationalGaussianProjection
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₁ where
  field
    scalarIntegralSameLiteralGaussian :
      ∀ depth →
      Bishop._≃_
        (Rich.scalarIntegral rich (suc depth))
        (UV.embed (Literal.literalBetaZ dataSet (suc depth)))

open RichBrillouinRationalGaussianProjection public

richBrillouinRationalGaussianProjectionLevel : ProofLevel
richBrillouinRationalGaussianProjectionLevel = conditional
