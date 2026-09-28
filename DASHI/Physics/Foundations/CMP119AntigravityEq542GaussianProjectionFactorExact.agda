{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEq542GaussianProjectionFactorExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Projection
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- FACTOR THE RICH/RATIONAL GAUSSIAN WELD THROUGH THE SOURCE EQ.(5.42) SCALAR
--
-- The cross-carrier equality
--
--   rich scalarIntegral ~= embed(rational literal beta_Z)
--
-- should not be proved by comparing two independently-normalized formulas.
-- Both sides are supposed to represent the SAME source-native Gaussian beta
-- coefficient extracted by the mixed p_mu p_nu derivative at p=0.
--
-- Expose that common rational source coordinate explicitly and prove the old
-- projection theorem by transitivity.
------------------------------------------------------------------------

record Eq542GaussianProjectionFactor
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₁ where
  field
    sourceGaussianBeta : Nat → ℚ

    richShellRepresentsSourceGaussian :
      ∀ depth →
      Bishop._≃_
        (Rich.scalarIntegral rich (suc depth))
        (UV.embed (sourceGaussianBeta depth))

    rationalPlaquetteRepresentsSourceGaussian :
      ∀ depth →
      Literal.literalBetaZ dataSet (suc depth)
      ≡ sourceGaussianBeta depth

open Eq542GaussianProjectionFactor public

asRichBrillouinRationalGaussianProjection :
  ∀ {dataSet rich} →
  Eq542GaussianProjectionFactor dataSet rich →
  Projection.RichBrillouinRationalGaussianProjection dataSet rich
asRichBrillouinRationalGaussianProjection factor = record
  { Projection.RichBrillouinRationalGaussianProjection.scalarIntegralSameLiteralGaussian =
      λ depth →
        BishopP.≃-trans
          (richShellRepresentsSourceGaussian factor depth)
          (BishopP.≃-symm
            (UV.embedEquality
              (rationalPlaquetteRepresentsSourceGaussian factor depth)))
  }

eq542GaussianProjectionFactorCompilerLevel : ProofLevel
eq542GaussianProjectionFactorCompilerLevel = machineChecked

richShellToEq542SourceIdentificationLevel : ProofLevel
richShellToEq542SourceIdentificationLevel = conditional

rationalPlaquetteToEq542SourceIdentificationLevel : ProofLevel
rationalPlaquetteToEq542SourceIdentificationLevel = conditional
