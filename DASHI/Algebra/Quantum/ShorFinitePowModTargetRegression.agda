module DASHI.Algebra.Quantum.ShorFinitePowModTargetRegression where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin; toℕ)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Crypto.RSAArithmeticCore as RSA
import DASHI.Algebra.Quantum.ShorFinitePowModTargetExact as Target

------------------------------------------------------------------------
-- RED regression: RSA.powMod must inhabit the finite residue target Fin N,
-- retaining exact equality with the existing Nat-valued arithmetic object.
------------------------------------------------------------------------

powModTargetExists :
  (base exponent modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Fin modulus
powModTargetExists = Target.powModFiniteTarget

powModTargetRetainsExactNatValue :
  (base exponent modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  toℕ (Target.powModFiniteTarget base exponent modulus modulusNonZero)
  ≡ RSA.powMod base exponent modulus {{modulusNonZero}}
powModTargetRetainsExactNatValue = Target.powModFiniteTargetValue
