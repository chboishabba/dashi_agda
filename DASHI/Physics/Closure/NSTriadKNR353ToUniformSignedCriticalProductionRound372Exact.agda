module DASHI.Physics.Closure.NSTriadKNR353ToUniformSignedCriticalProductionRound372Exact where

------------------------------------------------------------------------
-- ROUND372 / BIDI: R353 SIGNED FAMILY -> ROUND104 SIGNED CRITICAL FAMILY
--
-- R353 already owns a cutoff-indexed family of R303 signed integrated Gram
-- payments with one cutoff-uniform upper envelope.  Round104's critical
-- consumer wants a cutoff-indexed `UniformSignedCriticalProductionFamily`.
--
-- These are not definitionally the same physical observable, so this adapter
-- does not equate them by name.  It asks for one explicit same-cutoff physical
-- realization of each R353 payment as the complete signed critical slice, plus
-- the uniform initial+remainder ceiling required by Round104.  The Round104
-- barrier algebra is then reused unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact as R303
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxFamilyToR293Round353Exact as R353
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed

record R353ToCriticalProductionInputs
    (Time : Set)
    (family : R353.SignedGramFluxFamilyInputs Nat Time) : Set₁ where
  field
    criticalSlice : Nat → Signed.IntegratedSignedCriticalSlice

    -- Same-cutoff/same-payment weld: the complete signed critical production
    -- consumed by Round104 is the exact signed integral paid by R303/R353.
    criticalProductionIsR303SignedIntegral :
      (N : Nat) →
      Signed.integratedSignedProduction (criticalSlice N)
      ≡ R303.signedGramIntegral (R353.gramFluxPayment family N)

    uniformCriticalCeiling : ℚ

    uniformInitialPlusRemainder :
      (N : Nat) →
      Signed.initialCritical (criticalSlice N)
        + Signed.integrableRemainder (criticalSlice N)
      ≤ uniformCriticalCeiling

open R353ToCriticalProductionInputs public

r353BuildsUniformSignedCriticalProductionFamily :
  (Time : Set) →
  (family : R353.SignedGramFluxFamilyInputs Nat Time) →
  R353ToCriticalProductionInputs Time family →
  Signed.UniformSignedCriticalProductionFamily
r353BuildsUniformSignedCriticalProductionFamily Time family I =
  Signed.uniform-signed-critical-production-family
    Nat
    (criticalSlice I)
    (uniformCriticalCeiling I)
    (uniformInitialPlusRemainder I)

r353CriticalFamilyGetsUniformGalerkinBarrier :
  (Time : Set) →
  (family : R353.SignedGramFluxFamilyInputs Nat Time) →
  (I : R353ToCriticalProductionInputs Time family) →
  (N : Nat) →
  Signed.terminalCritical (criticalSlice I N)
    + Signed.retainedViscosity (criticalSlice I N)
        * Signed.criticalDissipation (criticalSlice I N)
  ≤ uniformCriticalCeiling I
r353CriticalFamilyGetsUniformGalerkinBarrier Time family I N =
  Signed.uniformGalerkinSignedCriticalProduction
    (r353BuildsUniformSignedCriticalProductionFamily Time family I)
    N

round372R353CutoffFamilyReusedDirectly : Bool
round372R353CutoffFamilyReusedDirectly = true

round372R303SignedIntegralMustMatchCriticalProductionExplicitly : Bool
round372R303SignedIntegralMustMatchCriticalProductionExplicitly = true

round372SignedGramNamedAsCriticalProductionWithoutReceipt : Bool
round372SignedGramNamedAsCriticalProductionWithoutReceipt = false

round372Round104BarrierAlgebraReused : Bool
round372Round104BarrierAlgebraReused = true

round372UniformCriticalBarrierCompilerClosedConditionally : Bool
round372UniformCriticalBarrierCompilerClosedConditionally = true

round372UniformCriticalBarrierCompilerClosedConditionallyIsTrue :
  round372UniformCriticalBarrierCompilerClosedConditionally ≡ true
round372UniformCriticalBarrierCompilerClosedConditionallyIsTrue = refl

round372SignedGramNamedAsCriticalProductionWithoutReceiptIsFalse :
  round372SignedGramNamedAsCriticalProductionWithoutReceipt ≡ false
round372SignedGramNamedAsCriticalProductionWithoutReceiptIsFalse = refl
