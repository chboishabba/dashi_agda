{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEq542GaussianProjectionFactorExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

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
--   rich coefficient ~= embed(rational literal beta_Z)
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

    richCoefficientRepresentsSourceGaussian :
      ∀ depth →
      Bishop._≃_
        (Rich.coefficient rich depth)
        (UV.embed (sourceGaussianBeta depth))

    rationalPlaquetteRepresentsSourceGaussian :
      ∀ depth →
      Literal.literalBetaZ dataSet depth
      ≡ sourceGaussianBeta depth

open Eq542GaussianProjectionFactor public

asRichBrillouinRationalGaussianProjection :
  ∀ {dataSet rich} →
  Eq542GaussianProjectionFactor dataSet rich →
  Projection.RichBrillouinRationalGaussianProjection dataSet rich
asRichBrillouinRationalGaussianProjection factor = record
  { Projection.RichBrillouinRationalGaussianProjection.coefficientSameLiteralGaussian =
      λ depth →
        BishopP.≃-trans
          (richCoefficientRepresentsSourceGaussian factor depth)
          (subst
            (λ selected →
              Bishop._≃_
                (UV.embed selected)
                (UV.embed (Literal.literalBetaZ dataSet depth)))
            (rationalPlaquetteRepresentsSourceGaussian factor depth)
            BishopP.≃-refl)
  }

eq542GaussianProjectionFactorCompilerLevel : ProofLevel
eq542GaussianProjectionFactorCompilerLevel = machineChecked

richCoefficientToEq542SourceIdentificationLevel : ProofLevel
richCoefficientToEq542SourceIdentificationLevel = conditional

rationalPlaquetteToEq542SourceIdentificationLevel : ProofLevel
rationalPlaquetteToEq542SourceIdentificationLevel = conditional
