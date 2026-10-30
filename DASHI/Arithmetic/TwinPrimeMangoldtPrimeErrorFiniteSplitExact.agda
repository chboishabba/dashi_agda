module DASHI.Arithmetic.TwinPrimeMangoldtPrimeErrorFiniteSplitExact where

------------------------------------------------------------------------
-- M14/M15: EXACT FINITE PRIME-ONLY + NON-PRIME CORRELATION SPLIT.
--
-- Original mathematical root: von Mangoldt/prime-power weighting.
-- Imported proof owners: original RiemannVonMangoldtSpecification,
-- original exhaustive endpoint cases, and M14 actual finite sum.
--
-- A pointwise exhaustive case split separates the true (p,p+2)
-- exponent-one branch from ALL remaining prime-power contributions.
-- Finite sum reordering requires EXPLICIT additive interchange.
-- Neither WeilTestSpace nor an arbitrary AdditiveScalar promises it.
-- No positivity estimate / logarithmic error estimate is claimed.
-- All theorem terms source-written, Agda kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans; sym)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Arithmetic.TwinPrimeMangoldtExhaustiveSupportCaseExact as Cases
import DASHI.Arithmetic.TwinPrimeMangoldtClassifiedFiniteSumExact as Classified
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Residual
import DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact as Actual
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeWeilActualCorrelationPartitionExact as WeilBridge

record AdditiveInterchangeLaws (space : Weil.WeilTestSpace) : Set where
  field
    zeroLeft : (x : Weil.WeilTestSpace.Scalar space) →
      Weil.WeilTestSpace._+S_ space
        (Weil.WeilTestSpace.zeroS space) x ≡ x
    zeroRight : (x : Weil.WeilTestSpace.Scalar space) →
      Weil.WeilTestSpace._+S_ space x
        (Weil.WeilTestSpace.zeroS space) ≡ x
    interchange : (a b c d : Weil.WeilTestSpace.Scalar space) →
      Weil.WeilTestSpace._+S_ space
        (Weil.WeilTestSpace._+S_ space a b)
        (Weil.WeilTestSpace._+S_ space c d)
      ≡ Weil.WeilTestSpace._+S_ space
          (Weil.WeilTestSpace._+S_ space a c)
          (Weil.WeilTestSpace._+S_ space b d)
open AdditiveInterchangeLaws public

-- Only both exponent-one classifications are original prime/prime
-- weights. This is NOT the same predicate as "nonzero Lambda pair".
primeOnlyWeight :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space) →
  {n : Nat} →
  (l : Cases.MangoldtSupportCase space arithmetic n) →
  (r : Cases.MangoldtSupportCase space arithmetic (n + 2)) →
  Weil.WeilTestSpace.Scalar space
primeOnlyWeight space arithmetic
    (Cases.exponentOne p ep) (Cases.exponentOne q eq) =
  VM.AllPrimeArithmetic._*S_ arithmetic
    (VM.AllPrimeArithmetic.logPrimeWeight arithmetic p)
    (VM.AllPrimeArithmetic.logPrimeWeight arithmetic q)
primeOnlyWeight space arithmetic l r = Weil.WeilTestSpace.zeroS space

-- The residual explicitly retains every other term; outside-support
-- values may be 0 by original multiplication-zero laws, but are not
-- silently assumed 0 here.
nonPrimeErrorWeight :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space) →
  {n : Nat} →
  (l : Cases.MangoldtSupportCase space arithmetic n) →
  (r : Cases.MangoldtSupportCase space arithmetic (n + 2)) →
  Weil.WeilTestSpace.Scalar space
nonPrimeErrorWeight space arithmetic
    (Cases.exponentOne p ep) (Cases.exponentOne q eq) =
  Weil.WeilTestSpace.zeroS space
nonPrimeErrorWeight space arithmetic l r =
  Classified.pairSupportWeight space arithmetic (l , r)

-- Exact 9-case algebraic equality. The two additive unit laws are
-- required rather than invented by the phrase "Weil scalar".
pairCaseSplit :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (laws : AdditiveInterchangeLaws space) →
  {n : Nat} →
  (l : Cases.MangoldtSupportCase space arithmetic n) →
  (r : Cases.MangoldtSupportCase space arithmetic (n + 2)) →
  Classified.pairSupportWeight space arithmetic (l , r)
  ≡ Weil.WeilTestSpace._+S_ space
      (primeOnlyWeight space arithmetic l r)
      (nonPrimeErrorWeight space arithmetic l r)

pairCaseSplit space arithmetic laws (Cases.exponentOne p ep) (Cases.exponentOne q eq) =
  sym (zeroRight laws
    (Classified.pairSupportWeight space arithmetic ((Cases.exponentOne p ep) , (Cases.exponentOne q eq))))

pairCaseSplit space arithmetic laws (Cases.exponentOne p ep) (Cases.exponentAtLeastTwo q k eq) =
  sym (zeroLeft laws
    (Classified.pairSupportWeight space arithmetic ((Cases.exponentOne p ep) , (Cases.exponentAtLeastTwo q k eq))))

pairCaseSplit space arithmetic laws (Cases.exponentOne p ep) (Cases.noPrimePower outR) =
  sym (zeroLeft laws
    (Classified.pairSupportWeight space arithmetic ((Cases.exponentOne p ep) , (Cases.noPrimePower outR))))

pairCaseSplit space arithmetic laws (Cases.exponentAtLeastTwo p k ep) (Cases.exponentOne q eq) =
  sym (zeroLeft laws
    (Classified.pairSupportWeight space arithmetic ((Cases.exponentAtLeastTwo p k ep) , (Cases.exponentOne q eq))))

pairCaseSplit space arithmetic laws (Cases.exponentAtLeastTwo p k ep) (Cases.exponentAtLeastTwo q j eq) =
  sym (zeroLeft laws
    (Classified.pairSupportWeight space arithmetic ((Cases.exponentAtLeastTwo p k ep) , (Cases.exponentAtLeastTwo q j eq))))

pairCaseSplit space arithmetic laws (Cases.exponentAtLeastTwo p k ep) (Cases.noPrimePower outR) =
  sym (zeroLeft laws
    (Classified.pairSupportWeight space arithmetic ((Cases.exponentAtLeastTwo p k ep) , (Cases.noPrimePower outR))))

pairCaseSplit space arithmetic laws (Cases.noPrimePower outL) (Cases.exponentOne q eq) =
  sym (zeroLeft laws
    (Classified.pairSupportWeight space arithmetic ((Cases.noPrimePower outL) , (Cases.exponentOne q eq))))

pairCaseSplit space arithmetic laws (Cases.noPrimePower outL) (Cases.exponentAtLeastTwo q j eq) =
  sym (zeroLeft laws
    (Classified.pairSupportWeight space arithmetic ((Cases.noPrimePower outL) , (Cases.exponentAtLeastTwo q j eq))))

pairCaseSplit space arithmetic laws (Cases.noPrimePower outL) (Cases.noPrimePower outR) =
  sym (zeroLeft laws
    (Classified.pairSupportWeight space arithmetic ((Cases.noPrimePower outL) , (Cases.noPrimePower outR))))


-- Materialize the exhaustive pair into two numeric consumers.
primeOnlyAtNat :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Nat → Weil.WeilTestSpace.Scalar space
primeOnlyAtNat space arithmetic mangoldt n =
  primeOnlyWeight space arithmetic
    (Cases.supportCaseFromActualMangoldt space arithmetic mangoldt n)
    (Cases.supportCaseFromActualMangoldt space arithmetic mangoldt (n + 2))

nonPrimeErrorAtNat :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Nat → Weil.WeilTestSpace.Scalar space
nonPrimeErrorAtNat space arithmetic mangoldt n =
  nonPrimeErrorWeight space arithmetic
    (Cases.supportCaseFromActualMangoldt space arithmetic mangoldt n)
    (Cases.supportCaseFromActualMangoldt space arithmetic mangoldt (n + 2))

classifiedPointwiseSplit :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (laws : AdditiveInterchangeLaws space) →
  (n : Nat) →
  Classified.classifiedPairWeight space arithmetic mangoldt n
  ≡ Weil.WeilTestSpace._+S_ space
      (primeOnlyAtNat space arithmetic mangoldt n)
      (nonPrimeErrorAtNat space arithmetic mangoldt n)
classifiedPointwiseSplit space arithmetic mangoldt laws n =
  pairCaseSplit space arithmetic laws
    (Cases.supportCaseFromActualMangoldt space arithmetic mangoldt n)
    (Cases.supportCaseFromActualMangoldt space arithmetic mangoldt (n + 2))

-- Fold-level algebraic split: order is NOT changed within either
-- component. The independent interchange law accounts for the
-- movement between prime-only and error subsequences.
finiteSumPointwiseSplit :
  (space : Weil.WeilTestSpace) →
  (laws : AdditiveInterchangeLaws space) →
  (f g h : Nat → Weil.WeilTestSpace.Scalar space) →
  ((n : Nat) →
     f n ≡ Weil.WeilTestSpace._+S_ space (g n) (h n)) →
  (start count : Nat) →
  Sum.sumInterval (WeilBridge.weilAdditive space) f start count
  ≡ Weil.WeilTestSpace._+S_ space
      (Sum.sumInterval (WeilBridge.weilAdditive space) g start count)
      (Sum.sumInterval (WeilBridge.weilAdditive space) h start count)
finiteSumPointwiseSplit space laws f g h pointwise start zero =
  sym (zeroLeft laws (Weil.WeilTestSpace.zeroS space))
finiteSumPointwiseSplit space laws f g h pointwise start (suc count) =
  trans
    (cong₂ (Weil.WeilTestSpace._+S_ space)
      (pointwise start)
      (finiteSumPointwiseSplit space laws f g h pointwise
        (suc start) count))
    (interchange laws
      (g start)
      (h start)
      (Sum.sumInterval (WeilBridge.weilAdditive space) g
        (suc start) count)
      (Sum.sumInterval (WeilBridge.weilAdditive space) h
        (suc start) count))

-- The complete useful finite identity for M15:
-- original actual weighted Λ-pair sum = genuine exponent-one
-- prime-pair contribution + ALL other prime-power contribution.
-- The error bound remains an independent ANALYTIC obligation.
finiteMangoldtPrimeErrorSplit :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (laws : AdditiveInterchangeLaws space) →
  (start count : Nat) →
  Sum.sumInterval (WeilBridge.weilAdditive space)
    (Residual.pairCorrelationAtNat
      (Actual.actualMangoldtPair space arithmetic mangoldt))
    start count
  ≡ Weil.WeilTestSpace._+S_ space
      (Sum.sumInterval (WeilBridge.weilAdditive space)
        (primeOnlyAtNat space arithmetic mangoldt) start count)
      (Sum.sumInterval (WeilBridge.weilAdditive space)
        (nonPrimeErrorAtNat space arithmetic mangoldt) start count)
finiteMangoldtPrimeErrorSplit space arithmetic mangoldt laws
    start count =
  trans
    (Classified.finiteCorrelationClassifiedExact
      space arithmetic mangoldt start count)
    (finiteSumPointwiseSplit space laws
      (Classified.classifiedPairWeight space arithmetic mangoldt)
      (primeOnlyAtNat space arithmetic mangoldt)
      (nonPrimeErrorAtNat space arithmetic mangoldt)
      (classifiedPointwiseSplit space arithmetic mangoldt laws)
      start count)
