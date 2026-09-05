module DASHI.Analysis.NonArchimedeanExplicitSquaredMixingPrefactorExact where

------------------------------------------------------------------------
-- EXPLICIT SQUARED MIXING PREFACTOR
--
-- The false source claim uses unit prefactor:
--
--   ||P_n^t||^2 <= 2^(-t).
--
-- For a normalized monomial shell of cycle length L, every one-step weight has
-- modulus <= 1.  If t = q L + r with 0 <= r < L, full cycles supply the
-- spectral-rate decay and the remainder can cost at most one.  Therefore a
-- deliberately crude, square-root-free envelope is
--
--   ||P^t|H_L||^2 <= 2^(L-1) * 2^(-t).
--
-- Across the dyadic tower through level n, the longest nontrivial odd cycle is
-- L_max = 2^(n-2), so one explicit finite whole-level candidate is
--
--   C_n^2 = 2^(2^(n-2)-1).
--
-- This file owns the exact finite prefactor coordinates and the producer
-- contract.  It does not silently assert the operator inequality: the latter
-- still needs the source monomial path-product bound and orthogonal-shell
-- assembly receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

maxOddCycleLength : Nat → Nat
maxOddCycleLength n = pow2 (n - 2)

crudeSquaredPrefactor : Nat → Nat
crudeSquaredPrefactor n = pow2 (maxOddCycleLength n - 1)

maxOddCycleLengthAt3 : maxOddCycleLength 3 ≡ 2
maxOddCycleLengthAt3 = refl

crudeSquaredPrefactorAt3 : crudeSquaredPrefactor 3 ≡ 2
crudeSquaredPrefactorAt3 = refl

maxOddCycleLengthAt4 : maxOddCycleLength 4 ≡ 4
maxOddCycleLengthAt4 = refl

crudeSquaredPrefactorAt4 : crudeSquaredPrefactor 4 ≡ 8
crudeSquaredPrefactorAt4 = refl

record SquaredPrefactorProducer : Set₁ where
  field
    Shell State : Set
    level : Nat
    cycleLength : Shell → Nat
    shellMember : State → Shell → Set

    orthogonalShellDecomposition : Bool
    monomialCharacterAction : Bool
    normalizedOneStepWeightsAtMostOne : Bool
    exactFullCycleProductMagnitude : Bool
    cycleLengthsBoundedByMaxOddCycleLength : Bool

    shellSquaredPowerEnvelope :
      (shell : Shell) →
      Set
    wholeLevelSquaredPowerEnvelope : Set

open SquaredPrefactorProducer public

record ExplicitPrefactorAudit : Set where
  constructor explicitPrefactorAudit
  field
    finitePrefactorFormulaOwned : Bool
    sourceUnitPrefactorRefuted : Bool
    shellPathProductProducerLocated : Bool
    shellOrthogonalAssemblyLocated : Bool
    explicitWholeLevelOperatorBoundClosed : Bool
    optimalPrefactorRequiredForMixing : Bool

canonicalExplicitPrefactorAudit : ExplicitPrefactorAudit
canonicalExplicitPrefactorAudit =
  explicitPrefactorAudit true true true false false false

finitePrefactorCoordinateOwned :
  ExplicitPrefactorAudit.finitePrefactorFormulaOwned
    canonicalExplicitPrefactorAudit
  ≡ true
finitePrefactorCoordinateOwned = refl

unitPrefactorRemainsRejected :
  ExplicitPrefactorAudit.sourceUnitPrefactorRefuted
    canonicalExplicitPrefactorAudit
  ≡ true
unitPrefactorRemainsRejected = refl

optimalPrefactorIsNotRequired :
  ExplicitPrefactorAudit.optimalPrefactorRequiredForMixing
    canonicalExplicitPrefactorAudit
  ≡ false
optimalPrefactorIsNotRequired = refl
