module DASHI.Physics.Closure.NSTriadKNComActiveNormalizedGramRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- DOI: no DOI assigned to the cited historical conference article.
--
-- ROUND 63 / B1 -> B1.5
--
-- Once the physical odd-P/Q row product is factorized through a genuinely
-- normalized Gram cell, the universal sanity bound is automatic:
--
--      0 <= pairProduct <= overlap <= 1.
--
-- This file keeps that cheap diagnostic independent of the special six-three
-- geometry.  The hard B3 theorem must therefore improve `overlap <= 1` to the
-- shell-dependent 17/64 and 65/512 bounds; it cannot hide normalization inside
-- the six-three comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram
import DASHI.Physics.Closure.NSTriadKNComNormalizedOverlapSanityRound63Exact as Normalized

record PhysicalActiveNormalizedOddPQGramSource : Set₁ where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification
    normalizedPairProduct : Nat → Nat → ℚ
    normalizedPairProductNonnegative : ∀ q r →
      0ℚ ≤ normalizedPairProduct q r

    shellDistance : Nat → Nat → Nat

    inactivePairProductZero : ∀ q r →
      Hat.supportActive support q r ≡ false →
      normalizedPairProduct q r ≡ 0ℚ

    activeNormalizedGramCell : ∀ q r →
      Hat.supportActive support q r ≡ true →
      Normalized.NormalizedGramInterferenceCell (shellDistance q r)

    activeProductIsNormalizedGram : ∀ q r →
      (active : Hat.supportActive support q r ≡ true) →
      normalizedPairProduct q r
      ≡ Gram.pairProduct
          (Normalized.gramCell (activeNormalizedGramCell q r active))

open PhysicalActiveNormalizedOddPQGramSource public

activeNormalizedOverlapBetweenZeroAndOne :
  (physical : PhysicalActiveNormalizedOddPQGramSource) →
  ∀ q r →
  (active : Hat.supportActive (support physical) q r ≡ true) →
  let cell = activeNormalizedGramCell physical q r active
  in 0ℚ ≤ Gram.overlap (Normalized.gramCell cell)
     × Gram.overlap (Normalized.gramCell cell) ≤ 1ℚ
activeNormalizedOverlapBetweenZeroAndOne physical q r active =
  Normalized.normalizedOverlapNonnegative cell ,
  Normalized.normalizedOverlapBelowOne cell
  where
  cell = activeNormalizedGramCell physical q r active

activeNormalizedPairProductBelowOne :
  (physical : PhysicalActiveNormalizedOddPQGramSource) →
  ∀ q r →
  (active : Hat.supportActive (support physical) q r ≡ true) →
  normalizedPairProduct physical q r ≤ 1ℚ
activeNormalizedPairProductBelowOne physical q r active =
  let
    cell = activeNormalizedGramCell physical q r active
    bound = Normalized.normalizedPairProductBelowOne cell
  in
  subst
    (λ lower → lower ≤ 1ℚ)
    (sym (activeProductIsNormalizedGram physical q r active))
    bound

round63B15UnitOverlapSanityDerivedFromNormalizedB1 : Bool
round63B15UnitOverlapSanityDerivedFromNormalizedB1 = true

round63B15UnitOverlapSanityDerivedFromNormalizedB1IsTrue :
  round63B15UnitOverlapSanityDerivedFromNormalizedB1 ≡ true
round63B15UnitOverlapSanityDerivedFromNormalizedB1IsTrue = refl
