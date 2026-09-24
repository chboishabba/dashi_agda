module DASHI.Physics.Closure.NSWholeSpaceFiniteConvolutionToContinuumExact where

------------------------------------------------------------------------
-- A / EXPLICIT FINITE CONVOLUTION QUADRATURE -> CONTINUUM ENERGY SQUARE
--
-- Compose:
--
--   NSWholeSpaceFiniteConvolutionQuadratureExact
--     finite translation reindexing
--       -> F_n ~= E_n^2
--
-- with:
--
--   NSWholeSpaceConvolutionQuadratureCompletionExact
--     E_n -> E
--     F_n -> F
--       -> F ~= E^2.
--
-- Hence the whole standard-analysis input needed by THIS convolution-energy
-- calculation is reduced to two same-object convergence statements for an
-- explicit sequence of finite quadratures.  Finite Fubini and multiplication
-- continuity are compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Physics.Closure.NSWholeSpaceFiniteConvolutionQuadratureExact as Finite
import DASHI.Physics.Closure.NSWholeSpaceConvolutionQuadratureCompletionExact as Completion

record ExplicitConvolutionQuadratureSequence : Set₁ where
  constructor explicit-convolution-quadrature-sequence
  field
    quadrature :
      Nat → Finite.FiniteTranslationReindexedConvolutionQuadrature

    continuumEnergy : BishopReal.ℝ
    continuumConvolutionMass : BishopReal.ℝ

    energyQuadraturesConverge :
      BishopSequence._ConvergesTo_
        (λ index → Finite.energyMass (quadrature index))
        continuumEnergy

    convolutionQuadraturesConverge :
      BishopSequence._ConvergesTo_
        (λ index → Finite.convolutionMass (quadrature index))
        continuumConvolutionMass

open ExplicitConvolutionQuadratureSequence public

asConvolutionQuadratureCompletion :
  ExplicitConvolutionQuadratureSequence →
  Completion.ConvolutionQuadratureCompletion
asConvolutionQuadratureCompletion Q =
  Completion.convolution-quadrature-completion
    (λ index → Finite.energyMass (quadrature Q index))
    (λ index → Finite.convolutionMass (quadrature Q index))
    (continuumEnergy Q)
    (continuumConvolutionMass Q)
    (λ index →
      Finite.finiteConvolutionFactorisation
        (quadrature Q index))
    (energyQuadraturesConverge Q)
    (convolutionQuadraturesConverge Q)

continuumConvolutionMassIsEnergySquare :
  (Q : ExplicitConvolutionQuadratureSequence) →
  BishopReal._≃_
    (continuumConvolutionMass Q)
    (BishopReal._*_
      (continuumEnergy Q)
      (continuumEnergy Q))
continuumConvolutionMassIsEnergySquare Q =
  Completion.continuumConvolutionMassIsEnergySquare
    (asConvolutionQuadratureCompletion Q)

finiteConvolutionFubiniInputRequired : Bool
finiteConvolutionFubiniInputRequired = false

continuumConvolutionFubiniInputRequired : Bool
continuumConvolutionFubiniInputRequired = false

sameObjectEnergyQuadratureConvergenceRequired : Bool
sameObjectEnergyQuadratureConvergenceRequired = true

sameObjectConvolutionQuadratureConvergenceRequired : Bool
sameObjectConvolutionQuadratureConvergenceRequired = true

convolutionEnergyFactorisationClosedModuloExplicitConvergence : Bool
convolutionEnergyFactorisationClosedModuloExplicitConvergence = true

clayPromotion : Bool
clayPromotion = false

finiteConvolutionFubiniInputRequiredIsFalse :
  finiteConvolutionFubiniInputRequired ≡ false
finiteConvolutionFubiniInputRequiredIsFalse = refl

continuumConvolutionFubiniInputRequiredIsFalse :
  continuumConvolutionFubiniInputRequired ≡ false
continuumConvolutionFubiniInputRequiredIsFalse = refl

sameObjectEnergyQuadratureConvergenceRequiredIsTrue :
  sameObjectEnergyQuadratureConvergenceRequired ≡ true
sameObjectEnergyQuadratureConvergenceRequiredIsTrue = refl

sameObjectConvolutionQuadratureConvergenceRequiredIsTrue :
  sameObjectConvolutionQuadratureConvergenceRequired ≡ true
sameObjectConvolutionQuadratureConvergenceRequiredIsTrue = refl

convolutionEnergyFactorisationClosedModuloExplicitConvergenceIsTrue :
  convolutionEnergyFactorisationClosedModuloExplicitConvergence ≡ true
convolutionEnergyFactorisationClosedModuloExplicitConvergenceIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
