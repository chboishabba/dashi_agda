module DASHI.Arithmetic.TwinPrimeWeilActualCorrelationPartitionExact where

------------------------------------------------------------------------
-- M11/M13 JOIN: ACTUAL RIEMANN/WEIL LAMBDA CORRELATION ↔ FINITE PERIODS
--
-- Keep original WeilTestSpace and its additive laws distinct:
-- WeilTestSpace provides zeroS and +S but does NOT assert monoid
-- associativity/identity. They are explicit requirements here,
-- not silently inferred from the record.
--
-- This joins the original VM specification to M13's exact
-- partial / complete period BIDI (no analytic positivity).
-- Date: 2026-10-30. Source-written; kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeMangoldtMultiPeriodConcatExact as Multi
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact as Actual
import DASHI.Arithmetic.TwinPrimeMangoldtPartialPeriodPartitionExact as Partial

weilAdditive : Weil.WeilTestSpace → Sum.AdditiveScalar
weilAdditive space = record
  { Scalar = Weil.WeilTestSpace.Scalar space
  ; zero = Weil.WeilTestSpace.zeroS space
  ; add = Weil.WeilTestSpace._+S_ space
  }

record WeilAdditiveLaws (space : Weil.WeilTestSpace) : Set where
  field
    leftZero :
      (x : Weil.WeilTestSpace.Scalar space) →
      Weil.WeilTestSpace._+S_ space
        (Weil.WeilTestSpace.zeroS space) x ≡ x

    addAssociative :
      (x y z : Weil.WeilTestSpace.Scalar space) →
      Weil.WeilTestSpace._+S_ space
        (Weil.WeilTestSpace._+S_ space x y) z
      ≡ Weil.WeilTestSpace._+S_ space x
          (Weil.WeilTestSpace._+S_ space y z)
open WeilAdditiveLaws public

weilMonoid :
  (space : Weil.WeilTestSpace) →
  WeilAdditiveLaws space →
  Multi.MonoidSum (weilAdditive space)
weilMonoid space laws = record
  { leftIdentity = leftZero laws
  ; associative = addAssociative laws
  }

-- Note that AllPrimeArithmetic still owns the actual lambda
-- interpretation. An arbitrary function Nat → Scalar cannot pass
-- for von Mangoldt merely because it is renamed.
realMangoldtPartialPeriodBidi :
  (space : Weil.WeilTestSpace) →
  (arithmetic : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (laws : WeilAdditiveLaws space) →
  (start prefixLen period blocks suffixLen : Nat) →
  start + prefixLen ≡ period * 270 →
  Sum.sumInterval (weilAdditive space)
    (Bidi.pairCorrelationAtNat
      (Actual.actualMangoldtPair space arithmetic mangoldt))
    start (prefixLen + (blocks * 270 + suffixLen))
  ≡
  Sum.add (weilAdditive space)
    (Sum.sumInterval (weilAdditive space)
      (Bidi.pairCorrelationAtNat
        (Actual.actualMangoldtPair space arithmetic mangoldt))
      start prefixLen)
    (Sum.add (weilAdditive space)
      (Multi.codeBlockRows (weilAdditive space)
        (Actual.actualMangoldtPair space arithmetic mangoldt)
        period blocks)
      (Sum.sumInterval (weilAdditive space)
        (Bidi.pairCorrelationAtNat
          (Actual.actualMangoldtPair space arithmetic mangoldt))
        (period * 270 + blocks * 270) suffixLen))
realMangoldtPartialPeriodBidi space arithmetic mangoldt laws
    start prefixLen period blocks suffixLen aligned =
  Partial.partialPeriodPartition
    (weilAdditive space) (weilMonoid space laws)
    (Actual.actualMangoldtPair space arithmetic mangoldt)
    start prefixLen period blocks suffixLen aligned
