module DASHI.Arithmetic.TwinPrimeNat270ConsumerGuidedStrictRefinementExact where

------------------------------------------------------------------------
-- Q25/Q26 + M04: CONCRETE CONSUMER-GUIDED RESIDUAL STRICTNESS
--
-- Reuses the original generic CEGAR/consumer-guided refinement
-- machinery, *not* a parallel invented notion of sufficient data.
--
-- Witness 59 vs 329: same Fin270 residue; different period index;
-- distinct genuine twin-primality answers (59/61 versus 329/331).
-- Source-written, Agda kernel pending. This establishes necessity
-- of retained residual, not a prime-distribution estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact as Twin
import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Consumer

coarseResidue : Nat → Fin 270
coarseResidue = Period.finiteResidue270

finePeriod : Nat → Period.NatPeriod270
finePeriod = Period.encodeNatPeriod270

forgetPeriod : Period.NatPeriod270 → Fin 270
forgetPeriod = Period.boundedResidue

coarseFactorsThroughFine : (n : Nat) →
  coarseResidue n ≡ forgetPeriod (finePeriod n)
coarseFactorsThroughFine n = refl

fiftyNineAnd329SameResidue :
  coarseResidue 59 ≡ coarseResidue 329
fiftyNineAnd329SameResidue = refl

fiftyNineAnd329DifferentPeriod :
  finePeriod 59 ≡ finePeriod 329 → ⊥
fiftyNineAnd329DifferentPeriod eq
  with cong Period.periodIndex eq
... | ()

strictPeriodRefinement :
  Refine.StrictProjectionRefinement coarseResidue finePeriod
strictPeriodRefinement =
  Refine.strictProjectionRefinement
    forgetPeriod
    coarseFactorsThroughFine
    59 329
    fiftyNineAnd329SameResidue
    fiftyNineAnd329DifferentPeriod

trueTwin59 : Twin.twinStartBool 59 ≡ true
trueTwin59 = refl

falseTwin329 : Twin.twinStartBool 329 ≡ false
falseTwin329 = refl

twinConsumerSeparates :
  Twin.twinStartBool 59 ≡ Twin.twinStartBool 329 → ⊥
twinConsumerSeparates eq with
  trans (sym trueTwin59) (trans eq falseTwin329)
... | ()

strictConsumerGuidedPeriodRefinement :
  Refine.ConsumerGuidedRefinement
    coarseResidue finePeriod Twin.twinStartBool
strictConsumerGuidedPeriodRefinement =
  Refine.consumerGuidedRefinement
    strictPeriodRefinement
    twinConsumerSeparates

-- The false statement "every real-twin consumer factors through
-- Fin270 alone" is refuted by the generic, source-owned theorem.
noActualTwinConsumerFromBareFin270 :
  Consumer.ConsumerDescent coarseResidue Twin.twinStartBool → ⊥
noActualTwinConsumerFromBareFin270 =
  Refine.consumerGuidedRefinementRefutesOldDescent
    strictConsumerGuidedPeriodRefinement

-- In contrast, the full period-index representation suffices for
-- ALL Nat consumers, as demonstrated in the existing BIDI module.
