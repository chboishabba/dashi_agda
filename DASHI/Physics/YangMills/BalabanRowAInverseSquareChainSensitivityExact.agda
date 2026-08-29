module DASHI.Physics.YangMills.BalabanRowAInverseSquareChainSensitivityExact where

------------------------------------------------------------------------
-- ROW A: g-DERIVATIVE + u=g^-2 CHAIN FACTOR -> SIXTH-ORDER SENSITIVITY
--
-- This is exact ordered-rational algebra for the high-alpha shooting route.
-- If a literal beta/remainder channel satisfies
--
--       |d beta / dg| <= C g^3
--
-- and the inverse-square coordinate contributes
--
--       |dg / du| <= (1/2) g^3,      u = g^-2,
--
-- then the direct shooting sensitivity satisfies
--
--       |d beta / du| <= (C/2) g^6.
--
-- The calculus identities and literal source identification remain separate
-- physical/analytic obligations.  This module proves the multiplication and
-- power bookkeeping only, so the extra smallness cannot be lost downstream.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

half : ℚ
half = + 1 / 2

cube : ℚ → ℚ
cube g = g * g * g

sixth : ℚ → ℚ
sixth g = cube g * cube g

record InverseSquareChainSensitivityData : Set₁ where
  field
    coupling coefficient : ℚ
    betaDerivativeMagnitude couplingDerivativeMagnitude directDerivativeMagnitude : ℚ

    betaDerivativeNonnegative : 0ℚ ≤ betaDerivativeMagnitude
    couplingDerivativeNonnegative : 0ℚ ≤ couplingDerivativeMagnitude

    betaDerivativeBound :
      betaDerivativeMagnitude ≤ coefficient * cube coupling

    inverseSquareChainBound :
      couplingDerivativeMagnitude ≤ half * cube coupling

    directDerivativeBelowProduct :
      directDerivativeMagnitude
      ≤ betaDerivativeMagnitude * couplingDerivativeMagnitude

open InverseSquareChainSensitivityData public

inverseSquareChainGivesSixthOrder :
  (dataSet : InverseSquareChainSensitivityData) →
  directDerivativeMagnitude dataSet
  ≤ (half * coefficient dataSet) * sixth (coupling dataSet)
inverseSquareChainGivesSixthOrder dataSet =
  let
    betaD = betaDerivativeMagnitude dataSet
    gD = couplingDerivativeMagnitude dataSet
    C = coefficient dataSet
    g = coupling dataSet

    productBound :
      betaD * gD
      ≤ (C * cube g) * (half * cube g)
    productBound =
      ℚP.*-mono-≤
        (betaDerivativeNonnegative dataSet)
        (betaDerivativeBound dataSet)
        (couplingDerivativeNonnegative dataSet)
        (inverseSquareChainBound dataSet)

    chained :
      directDerivativeMagnitude dataSet
      ≤ (C * cube g) * (half * cube g)
    chained = ℚP.≤-trans
      (directDerivativeBelowProduct dataSet)
      productBound
  in
  subst
    (λ upper → directDerivativeMagnitude dataSet ≤ upper)
    (ℚRing.solve-∀ C g)
    chained

rowAInverseSquareChainSuppressionAlgebraLevel : ProofLevel
rowAInverseSquareChainSuppressionAlgebraLevel = machineChecked

-- Physical/analytic leaves: obtain the g^3 derivative estimate from the SAME
-- literal channel majorants used for betaInt, and identify the derivative of
-- the source running coupling in the inverse-square coordinate.  Once those
-- are inhabited, this theorem upgrades the direct contribution to g^6.
literalBetaChannelCubicDerivativeSensitivityLevel : ProofLevel
literalBetaChannelCubicDerivativeSensitivityLevel = conditional

literalInverseSquareCouplingChainDerivativeLevel : ProofLevel
literalInverseSquareCouplingChainDerivativeLevel = conditional
