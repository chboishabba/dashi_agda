module DASHI.Arithmetic.TwinPrimeMangoldtNonzeroPrimeSumWitnessExact where

------------------------------------------------------------------------
-- M16 FINITE WITNESS: NONZERO *CERTIFIED* PRIME-ONLY SUM → TWIN.
--
-- Original prime decision owner: TwinPrimeCertifiedEnumeratorExact.
-- Original prime-carrier identity owner: ChebyshevPrimeOwnership.
-- Reuse: classified exponent-one pair weights and original NatPrime.
--
-- A nonzero finite sum of actual prime/prime weights cannot be built
-- out of zero terms. This is constructive because true Nat twin
-- primality is already decidable. No positivity, logarithm,
-- cancellation estimate, unbounded prime correlation, or same-
-- object Monster/word-orbit identification is assumed.
--
-- The unbounded NONZERO PRIME-ONLY SUM is an *explicit premise*.
-- Supplying it would still require new analytic mathematics.
-- Source-written, Agda kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (cong₂; sym; trans)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Analysis.ChebyshevPrimeCounting as Cheb
import DASHI.Analysis.NatPrimeCountingInstance as PrimeNat
import DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact as Enum
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import DASHI.Arithmetic.TwinPrimeMangoldtExhaustiveSupportCaseExact as Cases
import DASHI.Arithmetic.TwinPrimeMangoldtPrimeOneCertifiedBidiExact as Certified
import DASHI.Arithmetic.TwinPrimeMangoldtPrimeErrorFiniteSplitExact as Split
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeWeilActualCorrelationPartitionExact as WeilBridge

-- Constructive membership, with exact start and count.
data TwinInInterval : Nat → Nat → Set where
  here : ∀ {start count} →
    Twin.TwinPrimeAt start →
    TwinInInterval start (suc count)
  there : ∀ {start count} →
    TwinInInterval (suc start) count →
    TwinInInterval start (suc count)

data NoTwinInInterval : Nat → Nat → Set where
  empty : ∀ {start} → NoTwinInInterval start zero
  next : ∀ {start count} →
    (Twin.TwinPrimeAt start → ⊥) →
    NoTwinInInterval (suc start) count →
    NoTwinInInterval start (suc count)

-- Reuses ORIGINAL actual twin-prime decider.
finiteTwinSearch :
  (start count : Nat) →
  TwinInInterval start count ⊎ NoTwinInInterval start count
finiteTwinSearch start zero = inj₂ empty
finiteTwinSearch start (suc count) with Enum.twinPrimeAt? start
... | yes tw = inj₁ (here tw)
... | no notTwin with finiteTwinSearch (suc start) count
...   | inj₁ found = inj₁ (there found)
...   | inj₂ none = inj₂ (next notTwin none)

-- If the two ORIGINAL Mangoldt support certificates are both
-- exponent one, a true NatPrime pair follows via Chebyshev owner.
-- Otherwise primeOnlyWeight is definitionally zero.
primeOnlyWeightZeroIfNotTwin :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic) →
  (n : Nat) →
  (Twin.TwinPrimeAt n → ⊥) →
  Split.primeOnlyAtNat space arithmetic mangoldt n
    ≡ Weil.WeilTestSpace.zeroS space
primeOnlyWeightZeroIfNotTwin space arithmetic mangoldt
    theta ownership n notTwin
  with Cases.supportCaseFromActualMangoldt
    space arithmetic mangoldt n
     | Cases.supportCaseFromActualMangoldt
       space arithmetic mangoldt (n + 2)
... | Cases.exponentOne p ep | Cases.exponentOne q eq =
  ⊥-elim (notTwin
    (Certified.primeOnePairToTwin space arithmetic theta
      ownership n (Certified.prime-one-pair p q ep eq)))
... | Cases.exponentOne p ep | Cases.exponentAtLeastTwo q k eq = refl
... | Cases.exponentOne p ep | Cases.noPrimePower outside = refl
... | Cases.exponentAtLeastTwo p k ep | Cases.exponentOne q eq = refl
... | Cases.exponentAtLeastTwo p k ep | Cases.exponentAtLeastTwo q j eq = refl
... | Cases.exponentAtLeastTwo p k ep | Cases.noPrimePower outside = refl
... | Cases.noPrimePower outside | Cases.exponentOne q eq = refl
... | Cases.noPrimePower outside | Cases.exponentAtLeastTwo q j eq = refl
... | Cases.noPrimePower outsideL | Cases.noPrimePower outsideR = refl

-- Structural induction on an EXACT certified no-twin interval.
-- Zero is independent of logarithmic scalar interpretation, but
-- left identity must be supplied by the scalar law owner.
primeOnlySumZeroWithoutTwins :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic)
  (laws : Split.AdditiveInterchangeLaws space) →
  (start count : Nat) →
  NoTwinInInterval start count →
  Sum.sumInterval (WeilBridge.weilAdditive space)
    (Split.primeOnlyAtNat space arithmetic mangoldt)
    start count
  ≡ Weil.WeilTestSpace.zeroS space
primeOnlySumZeroWithoutTwins space arithmetic mangoldt
    theta ownership laws start zero empty = refl
primeOnlySumZeroWithoutTwins space arithmetic mangoldt
    theta ownership laws start (suc count) (next notTwin rest) =
  trans
    (cong₂ (Weil.WeilTestSpace._+S_ space)
      (primeOnlyWeightZeroIfNotTwin space arithmetic mangoldt
        theta ownership start notTwin)
      (primeOnlySumZeroWithoutTwins space arithmetic mangoldt
        theta ownership laws (suc start) count rest))
    (Split.zeroLeft laws (Weil.WeilTestSpace.zeroS space))

-- No choice, postulate or classical omitted case: the finite
-- original decider either provides a certified pair or refutes
-- every position, which contradicts the nonzero sum.
nonzeroPrimeOnlySumGivesTwin :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic)
  (laws : Split.AdditiveInterchangeLaws space) →
  (start count : Nat) →
  (Sum.sumInterval (WeilBridge.weilAdditive space)
    (Split.primeOnlyAtNat space arithmetic mangoldt)
    start count
     ≡ Weil.WeilTestSpace.zeroS space → ⊥) →
  TwinInInterval start count
nonzeroPrimeOnlySumGivesTwin space arithmetic mangoldt
    theta ownership laws start count nonzero
  with finiteTwinSearch start count
... | inj₁ found = found
... | inj₂ none = ⊥-elim (nonzero
    (primeOnlySumZeroWithoutTwins space arithmetic mangoldt
      theta ownership laws start count none))

-- Extract the actual arithmetic magnitude and TWO NatPrime proofs.
twinInIntervalReadout :
  ∀ {start count} →
  TwinInInterval start count →
  Σ Nat (λ p → (start ≤ p) × Twin.TwinPrimeAt p)
twinInIntervalReadout {start} (here tw) =
  start , (NP.≤-refl , tw)
twinInIntervalReadout {start} (there further)
  with twinInIntervalReadout further
... | p , (afterStart , tw) =
  p , (NP.≤-trans (NP.n≤1+n start) afterStart , tw)

-- FINAL CONDITIONAL GATE: to obtain infinitude, one still needs
-- arbitrarily late NONZERO prime-only sums (not merely an exact
-- period codec or a bounded gap >2).
twinUnboundedFromUnboundedNonzeroPrimeSums :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic)
  (laws : Split.AdditiveInterchangeLaws space) →
  (windowLength : Nat → Nat) →
  ((N : Nat) →
    (Sum.sumInterval (WeilBridge.weilAdditive space)
      (Split.primeOnlyAtNat space arithmetic mangoldt)
      N (windowLength N)
     ≡ Weil.WeilTestSpace.zeroS space → ⊥)) →
  (N : Nat) →
  Σ Nat (λ p → (N ≤ p) × Twin.TwinPrimeAt p)
twinUnboundedFromUnboundedNonzeroPrimeSums space arithmetic
    mangoldt theta ownership laws length nonzero N =
  twinInIntervalReadout
    (nonzeroPrimeOnlySumGivesTwin space arithmetic
      mangoldt theta ownership laws N (length N) (nonzero N))
