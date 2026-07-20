{-# OPTIONS --safe #-}
module DASHI.Core.KernelEigenMDLBridgeRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
open import DASHI.Algebra.TritSupportSignFactor
open import DASHI.Core.KernelEigenMDLBridge

------------------------------------------------------------------------
-- Concrete carrier witnesses for the cross-pollinated seams.

negSupportSurvivesInvolution :
  supportOf (inv neg) ≡ supportOf neg
negSupportSurvivesInvolution = support-inv-invariant neg

zeroSupportSurvivesInvolution :
  supportOf (inv zer) ≡ supportOf zer
zeroSupportSurvivesInvolution = support-inv-invariant zer

positiveEncodingFlipsOnlySign :
  encode (inv pos) ≡ supportSignInv (encode pos)
positiveEncodingFlipsOnlySign = encode-inv-equivariant pos

identityKernel : Trit → Trit
identityKernel t = t

negIdentityFixed : FixedPoint identityKernel neg
negIdentityFixed = record { fixed = refl }

record Unit : Set where
  constructor unit

forgetRepresentative : Trit → Unit
forgetRepresentative _ = unit

negIdentityQuotientStable :
  QuotientStable forgetRepresentative identityKernel neg
negIdentityQuotientStable = fixedPoint⇒quotientStable negIdentityFixed

negIdentityPeriodic : PeriodicOrbit identityKernel neg
negIdentityPeriodic = record
  { predecessorPeriod = 0
  ; closes = refl
  }

negIdentityPeriodicQuotientClosure :
  forgetRepresentative
    (iterate (suc (predecessorPeriod negIdentityPeriodic)) identityKernel neg)
    ≡ forgetRepresentative neg
negIdentityPeriodicQuotientClosure =
  periodicOrbit⇒quotientClosure negIdentityPeriodic
