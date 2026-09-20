module DASHI.Physics.Closure.NSWholeSpaceConvolutionQuadratureCompletionExact where

------------------------------------------------------------------------
-- A / FINITE CONVOLUTION QUADRATURE -> CONTINUUM ENERGY FACTORISATION
--
-- The repo already owns exact finite rectangular Fubini mathematics.  The
-- genuinely continuum step is therefore not another Fubini axiom: it is the
-- completion statement identifying a sequence of finite convolution
-- quadratures with the selected whole-space integrals.
--
-- Suppose
--
--   E_n = finite energy mass,
--   F_n = finite convolution-product mass,
--
-- and every finite quadrature satisfies the exact factorisation
--
--   F_n ~= E_n * E_n.
--
-- If E_n -> E and F_n -> F in the imported Bishop real backend, continuity of
-- multiplication gives E_n^2 -> E^2; termwise equivalence transports this to
-- F_n -> E^2; uniqueness of Bishop limits then yields
--
--   F ~= E^2.
--
-- Thus Fubini/translation need only be proved on finite quadratures.  The
-- continuum trust boundary is narrowed to same-object quadrature convergence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

record ConvolutionQuadratureCompletion : Set₁ where
  constructor convolution-quadrature-completion
  field
    energyApprox : Nat → BishopReal.ℝ
    convolutionApprox : Nat → BishopReal.ℝ

    continuumEnergy : BishopReal.ℝ
    continuumConvolutionMass : BishopReal.ℝ

    finiteConvolutionFactorisation :
      (index : Nat) →
      BishopReal._≃_
        (convolutionApprox index)
        (BishopReal._*_
          (energyApprox index)
          (energyApprox index))

    energyApproxConverges :
      BishopSequence._ConvergesTo_
        energyApprox
        continuumEnergy

    convolutionApproxConverges :
      BishopSequence._ConvergesTo_
        convolutionApprox
        continuumConvolutionMass

open ConvolutionQuadratureCompletion public

energySquareApprox :
  ConvolutionQuadratureCompletion →
  Nat → BishopReal.ℝ
energySquareApprox C index =
  BishopReal._*_
    (energyApprox C index)
    (energyApprox C index)

energySquareApproxConverges :
  (C : ConvolutionQuadratureCompletion) →
  BishopSequence._ConvergesTo_
    (energySquareApprox C)
    (BishopReal._*_
      (continuumEnergy C)
      (continuumEnergy C))
energySquareApproxConverges C =
  BishopSequence.xₙyₙ→x₀y₀
    (continuumEnergy C , energyApproxConverges C)
    (continuumEnergy C , energyApproxConverges C)

convolutionApproxConvergesToEnergySquare :
  (C : ConvolutionQuadratureCompletion) →
  BishopSequence._ConvergesTo_
    (convolutionApprox C)
    (BishopReal._*_
      (continuumEnergy C)
      (continuumEnergy C))
convolutionApproxConvergesToEnergySquare C =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    {xs = energySquareApprox C}
    {ys = convolutionApprox C}
    (λ index {{_}} →
      BishopP.≃-symm
        (finiteConvolutionFactorisation C index))
    ( BishopReal._*_
        (continuumEnergy C)
        (continuumEnergy C)
    , energySquareApproxConverges C
    )

continuumConvolutionMassIsEnergySquare :
  (C : ConvolutionQuadratureCompletion) →
  BishopReal._≃_
    (continuumConvolutionMass C)
    (BishopReal._*_
      (continuumEnergy C)
      (continuumEnergy C))
continuumConvolutionMassIsEnergySquare C =
  BishopP.≃-symm
    (BishopSequence.uniqueness-of-limits
      (convolutionApproxConverges C)
      (convolutionApproxConvergesToEnergySquare C))

finiteFubiniMayBeDischargedBeforeCompletion : Bool
finiteFubiniMayBeDischargedBeforeCompletion = true

continuumFubiniAxiomRequiredByThisCompiler : Bool
continuumFubiniAxiomRequiredByThisCompiler = false

multiplicationContinuityImportedFromBishopBackend : Bool
multiplicationContinuityImportedFromBishopBackend = true

limitUniquenessImportedFromBishopBackend : Bool
limitUniquenessImportedFromBishopBackend = true

remainingInputIsSameObjectQuadratureConvergence : Bool
remainingInputIsSameObjectQuadratureConvergence = true

clayPromotion : Bool
clayPromotion = false

finiteFubiniMayBeDischargedBeforeCompletionIsTrue :
  finiteFubiniMayBeDischargedBeforeCompletion ≡ true
finiteFubiniMayBeDischargedBeforeCompletionIsTrue = refl

continuumFubiniAxiomRequiredByThisCompilerIsFalse :
  continuumFubiniAxiomRequiredByThisCompiler ≡ false
continuumFubiniAxiomRequiredByThisCompilerIsFalse = refl

multiplicationContinuityImportedFromBishopBackendIsTrue :
  multiplicationContinuityImportedFromBishopBackend ≡ true
multiplicationContinuityImportedFromBishopBackendIsTrue = refl

limitUniquenessImportedFromBishopBackendIsTrue :
  limitUniquenessImportedFromBishopBackend ≡ true
limitUniquenessImportedFromBishopBackendIsTrue = refl

remainingInputIsSameObjectQuadratureConvergenceIsTrue :
  remainingInputIsSameObjectQuadratureConvergence ≡ true
remainingInputIsSameObjectQuadratureConvergenceIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
