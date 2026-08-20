module DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 where

------------------------------------------------------------------------
-- Lightweight normalized B-leaf.
--
-- ROUND 62 AUTHORITY CORRECTION
--
-- This historical record is Q-valued.  The literal odd-(P/Q) Fourier
-- coefficients live in the selected physical real/complex carrier, so a
-- Q-valued `normalizedSquaredGramEnergy` CANNOT by itself be cited as the
-- literal physical operator-product energy.  Keep this module as the exact
-- rational certificate/majorant leaf used by the finite 17/64, 65/512 and
-- 133/256 arithmetic only.
--
-- Carrier-correct same-object physical authority now lives in
--
--   NSTriadKNComOrderedPhysicalMajorantRound62Exact
--
-- where normalized energy remains in `Carrier (realField model)` and rational
-- targets enter only through an ordered rational embedding of THAT carrier.
-- `NSTriadKNComBishopNormalizedMajorantRound62Exact` is a concrete setoid-real
-- comparison backend, not a definitional identification with the literal
-- Fourier `RealField`.
--
-- The record name `PhysicalNormalizedOddPQGramRealization` is retained for
-- dependency compatibility with earlier rounds; its authority is explicitly
-- narrowed here.  It is NOT a same-object physical realization theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _≤_)
import Data.Integer.Base as Int

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as HatWidth

sameShellTarget adjacentShellTarget : ℚ
sameShellTarget = Int.+ 17 / 64
adjacentShellTarget = Int.+ 65 / 512

record PhysicalNormalizedOddPQGramRealization
    (support : Hat.PhysicalOddPQCommonHatIdentification) : Set₁ where
  field
    -- ROUND62: rational certificate quantity only.  Do not identify this with
    -- the literal physical Fourier energy without an explicit ordered-real
    -- embedding/comparison theorem.
    normalizedSquaredGramEnergy : Nat → Nat → ℚ
    normalizedSquaredGramEnergyNonnegative :
      ∀ q r → 0ℚ ≤ normalizedSquaredGramEnergy q r

open PhysicalNormalizedOddPQGramRealization public

pairProduct :
  {support : Hat.PhysicalOddPQCommonHatIdentification} →
  PhysicalNormalizedOddPQGramRealization support → Nat → Nat → ℚ
pairProduct realization = normalizedSquaredGramEnergy realization

pairProductNonnegative :
  {support : Hat.PhysicalOddPQCommonHatIdentification} →
  (realization : PhysicalNormalizedOddPQGramRealization support) →
  ∀ q r → 0ℚ ≤ pairProduct realization q r
pairProductNonnegative realization =
  normalizedSquaredGramEnergyNonnegative realization

record SameAdjacentNormalizedFibreMassBounds
    {support : Hat.PhysicalOddPQCommonHatIdentification}
    (realization : PhysicalNormalizedOddPQGramRealization support) : Set where
  field
    sameShellBound : ∀ q →
      Hat.supportActive support q q ≡ true →
      pairProduct realization q q ≤ sameShellTarget

    forwardAdjacentBound : ∀ q →
      Hat.supportActive support q (suc q) ≡ true →
      pairProduct realization q (suc q) ≤ adjacentShellTarget

    reverseAdjacentBound : ∀ q →
      Hat.supportActive support (suc q) q ≡ true →
      pairProduct realization (suc q) q ≤ adjacentShellTarget

open SameAdjacentNormalizedFibreMassBounds public

normalizedActivePairWithinOne :
  {support : Hat.PhysicalOddPQCommonHatIdentification}
  (realization : PhysicalNormalizedOddPQGramRealization support) →
  ∀ q r →
  Hat.supportActive support q r ≡ true →
  HatWidth.WithinOne q r
normalizedActivePairWithinOne {support = support} realization q r active =
  Hat.commonHatWidthOne support q r active

rationalNormalizedGramIsOnlyCertificateCarrier : Bool
rationalNormalizedGramIsOnlyCertificateCarrier = true

rationalNormalizedGramIsLiteralPhysicalEnergy : Bool
rationalNormalizedGramIsLiteralPhysicalEnergy = false

rationalNormalizedGramIsOnlyCertificateCarrierIsTrue :
  rationalNormalizedGramIsOnlyCertificateCarrier ≡ true
rationalNormalizedGramIsOnlyCertificateCarrierIsTrue = refl

rationalNormalizedGramIsLiteralPhysicalEnergyIsFalse :
  rationalNormalizedGramIsLiteralPhysicalEnergy ≡ false
rationalNormalizedGramIsLiteralPhysicalEnergyIsFalse = refl
