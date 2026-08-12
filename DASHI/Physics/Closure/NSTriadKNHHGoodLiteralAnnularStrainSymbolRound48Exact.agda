module DASHI.Physics.Closure.NSTriadKNHHGoodLiteralAnnularStrainSymbolRound48Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- Remove one receipt-like HH-good seam.  On the repository's actual rational
-- projection-mode carrier define the annular matrix symbol literally by
--
--   m_ann(k,omega) = phi(k) m_strain(k,omega),
--
-- where `m_strain` is the already-constructed physical Fourier strain
-- multiplier.  If the annular cutoff is invariant under the selected positive
-- radial rescaling, the complete localized matrix symbol is order zero as an
-- exact theorem.
--
-- The remaining analytic task is now specifically to identify the inverse
-- Fourier transform of THIS symbol with an L1 master kernel and its canonical
-- torus periodization.  A scalar radial Luo kernel cannot inhabit this type.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain
import DASHI.Physics.Closure.NSTriadKNFourierStrainScaleInvariantRound40Exact as Scale

record LiteralAnnularStrainCutoff : Set₁ where
  field
    cutoffWeight : V.ProjectionMode → ℚ
    radialScaleInvariant :
      ∀ scale modeData →
      cutoffWeight (Scale.scaledProjectionMode scale modeData)
      ≡ cutoffWeight modeData

open LiteralAnnularStrainCutoff public

literalAnnularStrainSymbol :
  LiteralAnnularStrainCutoff →
  V.ProjectionMode → V.Vector3 → Matrix.Matrix3
literalAnnularStrainSymbol cutoff modeData omega =
  Strain.scaleMatrix
    (cutoffWeight cutoff modeData)
    (Strain.fourierStrainMultiplier modeData omega)

literalAnnularSymbolUsesPhysicalStrainMultiplier :
  ∀ cutoff modeData omega →
  literalAnnularStrainSymbol cutoff modeData omega
  ≡ Strain.scaleMatrix
      (cutoffWeight cutoff modeData)
      (Strain.fourierStrainMultiplier modeData omega)
literalAnnularSymbolUsesPhysicalStrainMultiplier cutoff modeData omega = refl

literalAnnularStrainSymbolScaleInvariant :
  ∀ cutoff scale modeData omega →
  literalAnnularStrainSymbol cutoff
    (Scale.scaledProjectionMode scale modeData) omega
  ≡ literalAnnularStrainSymbol cutoff modeData omega
literalAnnularStrainSymbolScaleInvariant cutoff scale modeData omega =
  trans
    (cong
      (λ weight →
        Strain.scaleMatrix weight
          (Strain.fourierStrainMultiplier
            (Scale.scaledProjectionMode scale modeData) omega))
      (radialScaleInvariant cutoff scale modeData))
    (cong
      (Strain.scaleMatrix (cutoffWeight cutoff modeData))
      (Scale.fourierStrainMultiplierScaleInvariant scale modeData omega))

literalAnnularMatrixStrainSymbolConstructed : Bool
literalAnnularMatrixStrainSymbolConstructed = true

literalAnnularMatrixStrainSymbolOrderZero : Bool
literalAnnularMatrixStrainSymbolOrderZero = true

literalAnnularInverseFourierMasterKernelConstructed : Bool
literalAnnularInverseFourierMasterKernelConstructed = false

literalAnnularMatrixStrainSymbolConstructedIsTrue :
  literalAnnularMatrixStrainSymbolConstructed ≡ true
literalAnnularMatrixStrainSymbolConstructedIsTrue = refl

literalAnnularMatrixStrainSymbolOrderZeroIsTrue :
  literalAnnularMatrixStrainSymbolOrderZero ≡ true
literalAnnularMatrixStrainSymbolOrderZeroIsTrue = refl

literalAnnularInverseFourierMasterKernelConstructedIsFalse :
  literalAnnularInverseFourierMasterKernelConstructed ≡ false
literalAnnularInverseFourierMasterKernelConstructedIsFalse = refl
