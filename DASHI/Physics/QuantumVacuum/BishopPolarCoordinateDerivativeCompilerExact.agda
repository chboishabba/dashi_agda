module DASHI.Physics.QuantumVacuum.BishopPolarCoordinateDerivativeCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopFactorDerivativeProductExact as Product
import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Trig
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary

------------------------------------------------------------------------
-- TYPED BISHOP POLAR COORDINATE DERIVATIVES
--
-- Once the Round11 sine/cosine derivative authority is available, ordinary
-- first-order calculus is no longer a separate Casimir receipt.  The factor
-- derivative identity/scalar/product calculus compiles the four entries of
-- the polar Jacobian for
--
--   x(r,theta) = r cos(theta),
--   y(r,theta) = r sin(theta).
------------------------------------------------------------------------

record BishopPolarCoordinateDerivativeReceipt
    (P : Trig.Round11FactorInterchangeProblem)
    (radius theta : Bishop.ℝ) : Set₁ where
  field
    dxDr : Factor.BishopFactorDerivativeAt
      (λ r → Bishop._*_ r (Elementary.bishopCos (Trig.dataSet P) theta))
      radius
      (Elementary.bishopCos (Trig.dataSet P) theta)

    dxDtheta : Factor.BishopFactorDerivativeAt
      (λ angle → Bishop._*_ radius (Elementary.bishopCos (Trig.dataSet P) angle))
      theta
      (Bishop.-_
        (Bishop._*_ radius (Elementary.bishopSin (Trig.dataSet P) theta)))

    dyDr : Factor.BishopFactorDerivativeAt
      (λ r → Bishop._*_ r (Elementary.bishopSin (Trig.dataSet P) theta))
      radius
      (Elementary.bishopSin (Trig.dataSet P) theta)

    dyDtheta : Factor.BishopFactorDerivativeAt
      (λ angle → Bishop._*_ radius (Elementary.bishopSin (Trig.dataSet P) angle))
      theta
      (Bishop._*_ radius (Elementary.bishopCos (Trig.dataSet P) theta))

    reading : String

open BishopPolarCoordinateDerivativeReceipt public

constantDerivative :
  ∀ constant point →
  Factor.BishopFactorDerivativeAt
    (λ _ → constant)
    point Bishop.0ℝ
constantDerivative constant point =
  Factor.factorDerivativeCongruence
    (λ value → BishopP.≃-symm (BishopP.*-identityʳ constant))
    (BishopP.*-zeroʳ constant)
    (Factor.factorDerivativeScale constant
      (Factor.powerFactorDerivative 0 point))

radiusTimesConstantDerivative :
  ∀ constant radius →
  Factor.BishopFactorDerivativeAt
    (λ r → Bishop._*_ r constant)
    radius constant
radiusTimesConstantDerivative constant radius =
  Factor.factorDerivativeCongruence
    (λ r → BishopP.*-comm r constant)
    (BishopP.*-identityʳ constant)
    (Factor.factorDerivativeScale constant
      (Product.factorDerivativeIdentity radius))

compileBishopPolarCoordinateDerivatives :
  ∀ {P} →
  Trig.Round11FactorInterchangeAuthority P →
  (radius theta : Bishop.ℝ) →
  BishopPolarCoordinateDerivativeReceipt P radius theta
compileBishopPolarCoordinateDerivatives {P} A radius theta =
  let
    sin = Elementary.bishopSin (Trig.dataSet P)
    cos = Elementary.bishopCos (Trig.dataSet P)

    cosineScaledRaw : Factor.BishopFactorDerivativeAt
      (λ angle → Bishop._*_ radius (cos angle))
      theta
      (Bishop._*_ radius (Bishop.-_ (sin theta)))
    cosineScaledRaw =
      Factor.factorDerivativeScale radius (Trig.cosineDerivative A theta)

    cosineScaledTarget :
      Bishop._≃_
        (Bishop._*_ radius (Bishop.-_ (sin theta)))
        (Bishop.-_ (Bishop._*_ radius (sin theta)))
    cosineScaledTarget =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ r s → r ⊗ (⊝ s) ⊜ ⊝ (r ⊗ s))
        BishopP.≃-refl radius (sin theta)
  in record
    { dxDr = radiusTimesConstantDerivative (cos theta) radius
    ; dxDtheta =
        Factor.factorDerivativeCongruence
          (λ _ → BishopP.≃-refl)
          cosineScaledTarget
          cosineScaledRaw
    ; dyDr = radiusTimesConstantDerivative (sin theta) radius
    ; dyDtheta =
        Factor.factorDerivativeScale radius (Trig.sineDerivative A theta)
    ; reading =
        "The four polar coordinate derivative entries compile from the same Round11 Bishop sine/cosine derivative authority and the factor-derivative scalar/identity rules."
    }

record Status : Set where
  field
    bishopIdentityDerivativeOwned : Bool
    bishopProductRuleOwned : Bool
    polarCoordinateDerivativeCompilerOwned : Bool
    trigInterchangeAuthorityStillRequired : Bool

    bishopIdentityDerivativeOwnedIsTrue : bishopIdentityDerivativeOwned ≡ true
    bishopProductRuleOwnedIsTrue : bishopProductRuleOwned ≡ true
    polarCoordinateDerivativeCompilerOwnedIsTrue : polarCoordinateDerivativeCompilerOwned ≡ true
    trigInterchangeAuthorityStillRequiredIsTrue : trigInterchangeAuthorityStillRequired ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { bishopIdentityDerivativeOwned = true
  ; bishopProductRuleOwned = true
  ; polarCoordinateDerivativeCompilerOwned = true
  ; trigInterchangeAuthorityStillRequired = true
  ; bishopIdentityDerivativeOwnedIsTrue = refl
  ; bishopProductRuleOwnedIsTrue = refl
  ; polarCoordinateDerivativeCompilerOwnedIsTrue = refl
  ; trigInterchangeAuthorityStillRequiredIsTrue = refl
  }
