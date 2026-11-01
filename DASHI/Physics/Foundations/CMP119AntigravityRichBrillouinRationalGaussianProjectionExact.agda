{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact where

open import Agda.Builtin.Nat using (Nat)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- RICH BRILLOUIN FULL ONE-LOOP -> RATIONAL LITERAL beta_Z
--
-- IMPORTANT: `scalarIntegral` is only the universal logarithmic shell term.
-- The configured rich one-loop coefficient is
--
--   coefficient = scalarIntegral + regularRemainder.
--
-- The literal plaquette beta_Z is the full Gaussian/one-loop plaquette
-- coefficient.  Therefore the cross-carrier same-object seam is the FULL
-- rich `coefficient`, not `scalarIntegral` alone.
------------------------------------------------------------------------

record RichBrillouinRationalGaussianProjection
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₁ where
  field
    coefficientSameLiteralGaussian :
      ∀ depth →
      Bishop._≃_
        (Rich.coefficient rich depth)
        (UV.embed (Literal.literalBetaZ dataSet depth))

open RichBrillouinRationalGaussianProjection public

richBrillouinRationalGaussianProjectionLevel : ProofLevel
richBrillouinRationalGaussianProjectionLevel = conditional
