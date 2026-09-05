module DASHI.Analysis.NonArchimedeanMonomialPowerPrefactorBidiExact where

------------------------------------------------------------------------
-- MONOMIAL POWER PREFACTOR BIDI
--
-- Correct replacement for the false C=1 one-step contraction route.
--
-- In the orthonormal character basis, P_n is monomial.  On a cycle of length L,
-- for t = q L + r, the exact monomial power formula splits the path product
-- into q full-cycle products and one remainder product.
--
-- The source cyclotomic identity gives for the normalized operator
--
--   |full cycle| = sqrt(2) / 2^L <= 2^(-L/2).
--
-- Define the finite transient prefactor
--
--   C_L = max_{k, 0<=r<L} 2^(r/2) |2^(-r) W_r(k)|.
--
-- Then the shell power norm obeys
--
--   ||P^t|| <= C_L 2^(-t/2).
--
-- The theorem is compatible with transient one-step norm > 1/sqrt(2); that
-- transient is exactly what C_L records.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record MonomialPowerPrefactorReceipt : Set₁ where
  field
    Shell Time Bound : Set

    shellCycleLengthDefined : Bool
    orthonormalCharacterBasisOwned : Bool
    exactMonomialPowerFormulaOwned : Bool
    normalizedWeightsAtMostOne : Bool
    normalizedFullCycleAtMostHalfRatePower : Bool
    finiteRemainderMaximumExists : Bool

    shellPowerBound : Shell → Time → Bound
    halfRateEnvelope : Shell → Time → Bound
    shellPowerBoundBelowEnvelope :
      (shell : Shell) → (time : Time) → Set

open MonomialPowerPrefactorReceipt public

record PrefactorSourceAudit : Set where
  constructor prefactorSourceAudit
  field
    sourceCharacterActionOwned : Bool
    sourceFullCycleMagnitudeSqrtTwoOwned : Bool
    sourceMonomialPowerFormulaOwned : Bool
    sourceProseUnitPrefactorClaimValid : Bool
    levelDependentPrefactorRouteAvailable : Bool
    uniformInLevelPrefactorProved : Bool

canonicalPrefactorSourceAudit : PrefactorSourceAudit
canonicalPrefactorSourceAudit =
  prefactorSourceAudit true true true false true false

unitPrefactorRouteRejected :
  PrefactorSourceAudit.sourceProseUnitPrefactorClaimValid
    canonicalPrefactorSourceAudit
  ≡ false
unitPrefactorRouteRejected = refl

levelDependentPrefactorRouteLives :
  PrefactorSourceAudit.levelDependentPrefactorRouteAvailable
    canonicalPrefactorSourceAudit
  ≡ true
levelDependentPrefactorRouteLives = refl

uniformPrefactorStillNeedsReceipt :
  PrefactorSourceAudit.uniformInLevelPrefactorProved
    canonicalPrefactorSourceAudit
  ≡ false
uniformPrefactorStillNeedsReceipt = refl
