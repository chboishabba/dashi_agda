{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1GaussianWQRToJetRound108Exact where

------------------------------------------------------------------------
-- ROUND108 A1 GAUSSIAN HALF
--
-- The literal Gaussian background variation has W + Q + R pieces.  On the
-- selected off-diagonal Lorentz component the existing Fourier theorem kills
-- Q and R once their position-space variations are Lorentz diagonal.  Hence the
-- physical Gaussian mixed two-jet coefficient is reduced to the Wilson piece.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109MixedLorentzFourierVanishingExact as WQR
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as Jet

rationalFourierAlgebra : WQR.FourierScalarAlgebra ℚ
rationalFourierAlgebra = record
  { WQR.FourierScalarAlgebra.zero = 0ℚ
  ; WQR.FourierScalarAlgebra._+_ = _+_
  ; WQR.FourierScalarAlgebra._*_ = _*_
  ; WQR.FourierScalarAlgebra.zeroPlus = ℚP.+-identityˡ
  ; WQR.FourierScalarAlgebra.plusZero = ℚP.+-identityʳ
  ; WQR.FourierScalarAlgebra.timesZero = ℚP.*-zeroʳ
  }

record GaussianWQRJetIdentification
    (Position Momentum Lorentz : Set) : Set₁ where
  field
    wqr : WQR.MixedWQRCarrier
      Position Momentum Lorentz ℚ rationalFourierAlgebra
    momentum : Momentum
    μ ν : Lorentz
    offDiagonal : WQR.OffDiagonal (WQR.averagingVariation wqr) μ ν

    betaZ : ℚ
    gaussianJet : Jet.OffDiagonalTwoJet

    gaussianJetMixedIsWQR :
      Jet.mixedDerivativeCoefficient gaussianJet
      ≡ WQR.mixedWQR wqr momentum μ ν

    wilsonMixedIsNegativeBetaZ :
      WQR.wilsonMixed wqr momentum μ ν ≡ - betaZ

open GaussianWQRJetIdentification public

gaussianMixedIsNegativeBetaZ :
  ∀ {Position Momentum Lorentz}
    (dataSet : GaussianWQRJetIdentification Position Momentum Lorentz) →
  Jet.mixedDerivativeCoefficient (gaussianJet dataSet)
  ≡ - betaZ dataSet
gaussianMixedIsNegativeBetaZ dataSet =
  trans
    (gaussianJetMixedIsWQR dataSet)
    (trans
      (WQR.mixedWQREqualsWilson
        (wqr dataSet) (momentum dataSet) (μ dataSet) (ν dataSet)
        (offDiagonal dataSet))
      (wilsonMixedIsNegativeBetaZ dataSet))

round108GaussianWQRToJetLevel : ProofLevel
round108GaussianWQRToJetLevel = machineChecked

-- Physical leaves are now exactly the source-coordinate bindings:
-- * literal CMP98 DQ and CMP99 constrained DR instantiate the two diagonal
--   position variations in `wqr`;
-- * the selected Wilson mixed coefficient uses the same Gaussian normalization
--   as betaZ.  Q/R consume no patch margin after those bindings.
literalCMP98109WQRCarrierRound108Level : ProofLevel
literalCMP98109WQRCarrierRound108Level = conditional

literalCMP109WilsonMixedCoefficientNormalizationRound108Level : ProofLevel
literalCMP109WilsonMixedCoefficientNormalizationRound108Level = conditional
