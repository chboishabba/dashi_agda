module DASHI.Arithmetic.TwinPrimeMangoldtErrorSupportProperExact where

------------------------------------------------------------------------
-- M15: NONZERO RETAINED ERROR REQUIRES A PROPER POWER ENDPOINT.
--
-- Reuse the ORIGINAL VonMangoldtAt 3-way case split, source-written
-- PrimeErrorFiniteSplit and source-written explicit ProductZeroLaws.
-- Unlike the 27-wheel survivor count, this is about true prime-power
-- support in the unbounded Nat arithmetic.
--
-- For ANY Nat n, either the original retained "non-prime" term
-- is provably zero or n / n+2 carries a PROPER p^k (k>=2)
-- occurrence. Exactly the bridge needed to apply CT10
-- square-root/binary counting to CT13's finite error.
--
-- No bound on positive logs, no parity breakthrough and no
-- invented same-object Monster/Ibrahim/QID authority.
-- Source-written, Agda kernel pending, 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Arithmetic.TwinPrimeMangoldtExhaustiveSupportCaseExact as Cases
import DASHI.Arithmetic.TwinPrimeMangoldtPrimeErrorFiniteSplitExact as Split
import DASHI.Arithmetic.TwinPrimeMangoldtOutsidePrimePowersZeroExact as Zero

data ProperPowerAt
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (n : Nat) : Set where
  proper-power-at :
    (p : VM.AllPrimeArithmetic.Prime arithmetic) →
    (k : Nat) →
    n ≡ VM.primePowerNat space arithmetic p (suc k) →
    ProperPowerAt space arithmetic n

data ProperPowerAtEitherEndpoint
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (n : Nat) : Set where
  leftProper :
    ProperPowerAt space arithmetic n →
    ProperPowerAtEitherEndpoint space arithmetic n
  rightProper :
    ProperPowerAt space arithmetic (n + 2) →
    ProperPowerAtEitherEndpoint space arithmetic n

-- The only four branches with NO proper power are
-- exponent-one/exponent-one and the three outside-support
-- combinations. On an outside branch the zero law is explicit.
errorZeroIfNoProper :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (zeroLaws : Zero.ProductZeroLaws space arithmetic) →
  (n : Nat) →
  (ProperPowerAtEitherEndpoint space arithmetic n → ⊥) →
  Split.nonPrimeErrorAtNat space arithmetic mangoldt n
    ≡ Weil.WeilTestSpace.zeroS space
errorZeroIfNoProper space arithmetic mangoldt zeroLaws n noProper
  with Cases.supportCaseFromActualMangoldt
         space arithmetic mangoldt n
     | Cases.supportCaseFromActualMangoldt
         space arithmetic mangoldt (n + 2)
... | Cases.exponentOne p ep | Cases.exponentOne q eq = refl
... | Cases.exponentOne p ep | Cases.exponentAtLeastTwo q k eq =
  ⊥-elim (noProper (rightProper (proper-power-at q k eq)))
... | Cases.exponentOne p ep | Cases.noPrimePower outR =
  Zero.zeroRight zeroLaws
    (VM.AllPrimeArithmetic.logPrimeWeight arithmetic p)
... | Cases.exponentAtLeastTwo p k ep | Cases.exponentOne q eq =
  ⊥-elim (noProper (leftProper (proper-power-at p k ep)))
... | Cases.exponentAtLeastTwo p k ep
    | Cases.exponentAtLeastTwo q j eq =
  ⊥-elim (noProper (leftProper (proper-power-at p k ep)))
... | Cases.exponentAtLeastTwo p k ep | Cases.noPrimePower outR =
  ⊥-elim (noProper (leftProper (proper-power-at p k ep)))
... | Cases.noPrimePower outL | Cases.exponentOne q eq =
  Zero.zeroLeft zeroLaws
    (VM.AllPrimeArithmetic.logPrimeWeight arithmetic q)
... | Cases.noPrimePower outL | Cases.exponentAtLeastTwo q j eq =
  ⊥-elim (noProper (rightProper (proper-power-at q j eq)))
... | Cases.noPrimePower outL | Cases.noPrimePower outR =
  Zero.zeroLeft zeroLaws
    (Weil.WeilTestSpace.zeroS space)

-- Decidable support at a fixed n follows from the original
-- lambdaSpecified constructor; no independent prime search.
errorNonzeroHasProperPower :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (zeroLaws : Zero.ProductZeroLaws space arithmetic) →
  (n : Nat) →
  (Split.nonPrimeErrorAtNat space arithmetic mangoldt n
    ≡ Weil.WeilTestSpace.zeroS space → ⊥) →
  ProperPowerAtEitherEndpoint space arithmetic n
errorNonzeroHasProperPower space arithmetic mangoldt zeroLaws n
    nonzero
  with Cases.supportCaseFromActualMangoldt
         space arithmetic mangoldt n
     | Cases.supportCaseFromActualMangoldt
         space arithmetic mangoldt (n + 2)
... | Cases.exponentOne p ep | Cases.exponentOne q eq =
  ⊥-elim (nonzero refl)
... | Cases.exponentOne p ep | Cases.exponentAtLeastTwo q k eq =
  rightProper (proper-power-at q k eq)
... | Cases.exponentOne p ep | Cases.noPrimePower outR =
  ⊥-elim (nonzero
    (Zero.zeroRight zeroLaws
      (VM.AllPrimeArithmetic.logPrimeWeight arithmetic p)))
... | Cases.exponentAtLeastTwo p k ep | Cases.exponentOne q eq =
  leftProper (proper-power-at p k ep)
... | Cases.exponentAtLeastTwo p k ep
    | Cases.exponentAtLeastTwo q j eq =
  leftProper (proper-power-at p k ep)
... | Cases.exponentAtLeastTwo p k ep | Cases.noPrimePower outR =
  leftProper (proper-power-at p k ep)
... | Cases.noPrimePower outL | Cases.exponentOne q eq =
  ⊥-elim (nonzero
    (Zero.zeroLeft zeroLaws
      (VM.AllPrimeArithmetic.logPrimeWeight arithmetic q)))
... | Cases.noPrimePower outL | Cases.exponentAtLeastTwo q j eq =
  rightProper (proper-power-at q j eq)
... | Cases.noPrimePower outL | Cases.noPrimePower outR =
  ⊥-elim (nonzero
    (Zero.zeroLeft zeroLaws
      (Weil.WeilTestSpace.zeroS space)))
