module DASHI.Physics.Closure.NSWholeSpaceFiniteConvolutionSingleLimitExact where

------------------------------------------------------------------------
-- A / SINGLE-LIMIT COMPLETION FOR THE CONVOLUTION-ENERGY PRODUCT
--
-- The previous finite owner proves, for every explicit translation-reindexed
-- quadrature Q_n,
--
--   F_n ~= E_n * E_n.
--
-- Therefore convergence of F_n is NOT an independent standard-analysis
-- obligation once convergence of E_n is known.  Bishop continuity of
-- multiplication gives E_n^2 -> E^2, and the exact finite factorisation
-- transports that convergence to F_n.
--
-- This removes one of the two convergence inputs exposed by
-- NSWholeSpaceFiniteConvolutionToContinuumExact.  What remains is the genuine
-- same-object analytic task: construct energy quadratures for the selected
-- whole-space Fourier energy and identify their Bishop limit with the physical
-- R^3 energy integral.  No continuum Fubini/Tonelli axiom is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence
import RealProperties as BishopP

import DASHI.Physics.Closure.NSWholeSpaceFiniteConvolutionQuadratureExact as Finite

record SingleLimitConvolutionQuadratureSequence : Set₁ where
  constructor single-limit-convolution-quadrature-sequence
  field
    quadrature :
      Nat → Finite.FiniteTranslationReindexedConvolutionQuadrature

    continuumEnergy : BishopReal.ℝ

    energyQuadraturesConverge :
      BishopSequence._ConvergesTo_
        (λ index → Finite.energyMass (quadrature index))
        continuumEnergy

open SingleLimitConvolutionQuadratureSequence public

energySquareApprox :
  SingleLimitConvolutionQuadratureSequence →
  Nat → BishopReal.ℝ
energySquareApprox Q index =
  BishopReal._*_
    (Finite.energyMass (quadrature Q index))
    (Finite.energyMass (quadrature Q index))

convolutionApprox :
  SingleLimitConvolutionQuadratureSequence →
  Nat → BishopReal.ℝ
convolutionApprox Q index =
  Finite.convolutionMass (quadrature Q index)

energySquareApproxConverges :
  (Q : SingleLimitConvolutionQuadratureSequence) →
  BishopSequence._ConvergesTo_
    (energySquareApprox Q)
    (BishopReal._*_
      (continuumEnergy Q)
      (continuumEnergy Q))
energySquareApproxConverges Q =
  BishopSequence.xₙyₙ→x₀y₀
    (continuumEnergy Q , energyQuadraturesConverge Q)
    (continuumEnergy Q , energyQuadraturesConverge Q)

convolutionApproxEquivalentToEnergySquare :
  (Q : SingleLimitConvolutionQuadratureSequence) →
  (index : Nat) →
  BishopReal._≃_
    (convolutionApprox Q index)
    (energySquareApprox Q index)
convolutionApproxEquivalentToEnergySquare Q index =
  Finite.finiteConvolutionFactorisation
    (quadrature Q index)

convolutionApproxConvergesFromEnergyAlone :
  (Q : SingleLimitConvolutionQuadratureSequence) →
  BishopSequence._ConvergesTo_
    (convolutionApprox Q)
    (BishopReal._*_
      (continuumEnergy Q)
      (continuumEnergy Q))
convolutionApproxConvergesFromEnergyAlone Q =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    {xs = energySquareApprox Q}
    {ys = convolutionApprox Q}
    (λ index {{_}} →
      BishopP.≃-symm
        (convolutionApproxEquivalentToEnergySquare Q index))
    ( BishopReal._*_
        (continuumEnergy Q)
        (continuumEnergy Q)
    , energySquareApproxConverges Q
    )

independentConvolutionQuadratureConvergenceRequired : Bool
independentConvolutionQuadratureConvergenceRequired = false

continuumFubiniTonelliRequiredByThisCompletion : Bool
continuumFubiniTonelliRequiredByThisCompletion = false

energyQuadratureSameObjectConvergenceStillRequired : Bool
energyQuadratureSameObjectConvergenceStillRequired = true

convolutionLimitForcedByEnergyLimit : Bool
convolutionLimitForcedByEnergyLimit = true

clayPromotion : Bool
clayPromotion = false

independentConvolutionQuadratureConvergenceRequiredIsFalse :
  independentConvolutionQuadratureConvergenceRequired ≡ false
independentConvolutionQuadratureConvergenceRequiredIsFalse = refl

continuumFubiniTonelliRequiredByThisCompletionIsFalse :
  continuumFubiniTonelliRequiredByThisCompletion ≡ false
continuumFubiniTonelliRequiredByThisCompletionIsFalse = refl

energyQuadratureSameObjectConvergenceStillRequiredIsTrue :
  energyQuadratureSameObjectConvergenceStillRequired ≡ true
energyQuadratureSameObjectConvergenceStillRequiredIsTrue = refl

convolutionLimitForcedByEnergyLimitIsTrue :
  convolutionLimitForcedByEnergyLimit ≡ true
convolutionLimitForcedByEnergyLimitIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
