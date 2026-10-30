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
  (cong; cong₂; sym; trans; subst)

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
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Residual
import DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact as Actual

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

------------------------------------------------------------------------
-- CT09b: UPPER-BOUND PRESERVING FINITE INTERVAL WITNESS.
--
-- The original lower-only readout is retained for compatibility.
-- Here we also retain the strict upper endpoint:
--   start ≤ p < start + count.
-- This is a pure finite inductive property, NOT prime infinitude.
------------------------------------------------------------------------

twinInIntervalBoundedReadout :
  ∀ {start count} →
  TwinInInterval start count →
  Σ Nat (λ p →
    (start ≤ p) × ((suc p ≤ start + count) × Twin.TwinPrimeAt p))
twinInIntervalBoundedReadout {start} {suc count} (here tw) =
  start ,
    ( NP.≤-refl
    , (subst
        (λ end → suc start ≤ end)
        (sym (NP.+-suc start count))
        (NP.m≤m+n (suc start) count)
      , tw)
    )
twinInIntervalBoundedReadout {start} {suc count} (there further)
  with twinInIntervalBoundedReadout further
... | p , (lower , (upper , tw)) =
  p ,
    ( NP.≤-trans (NP.n≤1+n start) lower
    , (subst
        (λ end → suc p ≤ end)
        (sym (NP.+-suc start count))
        upper
      , tw)
    )

nonzeroPrimeOnlySumGivesBoundedTwin :
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
  Σ Nat (λ p →
    (start ≤ p) × ((suc p ≤ start + count) × Twin.TwinPrimeAt p))
nonzeroPrimeOnlySumGivesBoundedTwin
    space arithmetic mangoldt theta ownership laws
    start count nonzero =
  twinInIntervalBoundedReadout
    (nonzeroPrimeOnlySumGivesTwin
      space arithmetic mangoldt theta ownership laws
      start count nonzero)

------------------------------------------------------------------------
-- CT15/CT16 NEW ALTERNATE MAX CUT: EXACT TOTAL != ERROR SEPARATOR.
--
-- Original finite identity owner: finiteMangoldtPrimeErrorSplit.
-- Original finite witness owner: nonzeroPrimeOnlySumGivesBoundedTwin.
-- Neither a positive lower bound nor a real log scalar is necessary
-- for this LOGICAL implication. At arbitrarily large windows an
-- actual separator remains a genuinely OPEN number-theory task.
--
-- Consumer-guided premise: an observation of the actual scalar sums
-- differs. A noninjective observer is enough IF it distinguishes
-- these two concrete inputs. Mere residue-class data for n, QIDs,
-- character matches, and finite wheel survivors do not give it.
-- Source-written / Agda safe-kernel verification pending.
------------------------------------------------------------------------

actualMangoldtTotalWindow :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (start count : Nat) →
  Weil.WeilTestSpace.Scalar space
actualMangoldtTotalWindow space arithmetic mangoldt start count =
  Sum.sumInterval (WeilBridge.weilAdditive space)
    (Residual.pairCorrelationAtNat
      (Actual.actualMangoldtPair space arithmetic mangoldt))
    start count

actualMangoldtErrorWindow :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (start count : Nat) →
  Weil.WeilTestSpace.Scalar space
actualMangoldtErrorWindow space arithmetic mangoldt start count =
  Sum.sumInterval (WeilBridge.weilAdditive space)
    (Split.nonPrimeErrorAtNat space arithmetic mangoldt)
    start count

-- If prime-only sum were zero, exact split and additive left-zero
-- force total=error, contradicting the supplied actual mismatch.
totalErrorUnequalForcesPrimeOnlyNonzero :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (laws : Split.AdditiveInterchangeLaws space)
  (start count : Nat) →
  (actualMangoldtTotalWindow space arithmetic mangoldt start count
    ≡ actualMangoldtErrorWindow space arithmetic mangoldt start count
    → ⊥) →
  (Sum.sumInterval (WeilBridge.weilAdditive space)
    (Split.primeOnlyAtNat space arithmetic mangoldt)
    start count
    ≡ Weil.WeilTestSpace.zeroS space → ⊥)
totalErrorUnequalForcesPrimeOnlyNonzero
    space arithmetic mangoldt laws start count unequal primeZero =
  unequal
    (trans
      (Split.finiteMangoldtPrimeErrorSplit
        space arithmetic mangoldt laws start count)
      (trans
        (cong
          (λ x → Weil.WeilTestSpace._+S_ space x
            (actualMangoldtErrorWindow
              space arithmetic mangoldt start count))
          primeZero)
        (Split.zeroLeft laws
          (actualMangoldtErrorWindow
            space arithmetic mangoldt start count))))

-- A proof that the OBSERVED total differs from the OBSERVED error
-- is enough: any equality of original scalars would transport under
-- the observer via cong. This explicitly permits noninjective
-- observers but requires a real distinguishability proof.
observedTotalErrorSeparationGivesBoundedTwin :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic)
  (laws : Split.AdditiveInterchangeLaws space)
  {Observation : Set}
  (observe : Weil.WeilTestSpace.Scalar space → Observation)
  (start count : Nat) →
  (observe (actualMangoldtTotalWindow
    space arithmetic mangoldt start count)
    ≡
   observe (actualMangoldtErrorWindow
    space arithmetic mangoldt start count)
    → ⊥) →
  Σ Nat (λ p →
    (start ≤ p) × ((suc p ≤ start + count) × Twin.TwinPrimeAt p))
observedTotalErrorSeparationGivesBoundedTwin
    space arithmetic mangoldt theta ownership laws
    observe start count distinct =
  nonzeroPrimeOnlySumGivesBoundedTwin
    space arithmetic mangoldt theta ownership laws
    start count
    (totalErrorUnequalForcesPrimeOnlyNonzero
      space arithmetic mangoldt laws start count
      (λ equal → distinct (cong observe equal)))

-- CT18 CONDITIONAL COMPOSITION over arbitrarily late exact windows.
-- The input below is NOT a theorem proved in this module; it is the
-- precise new research obligation for parity/symmetry approaches.
cofinalObservedSeparationImpliesTwinInfinitude :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic)
  (laws : Split.AdditiveInterchangeLaws space)
  {Observation : Set}
  (observe : Weil.WeilTestSpace.Scalar space → Observation)
  (windowLength : Nat → Nat) →
  ((N : Nat) →
    (observe (actualMangoldtTotalWindow space arithmetic mangoldt
      N (windowLength N))
      ≡
     observe (actualMangoldtErrorWindow space arithmetic mangoldt
      N (windowLength N))
      → ⊥)) →
  Twin.TwinPrimesInfinitelyOften
cofinalObservedSeparationImpliesTwinInfinitude
    space arithmetic mangoldt theta ownership laws
    observe windowLength distinct =
  twinUnboundedFromUnboundedNonzeroPrimeSums
    space arithmetic mangoldt theta ownership laws
    windowLength
    (λ N →
      totalErrorUnequalForcesPrimeOnlyNonzero
        space arithmetic mangoldt laws N (windowLength N)
        (λ equal → distinct N (cong observe equal)))
