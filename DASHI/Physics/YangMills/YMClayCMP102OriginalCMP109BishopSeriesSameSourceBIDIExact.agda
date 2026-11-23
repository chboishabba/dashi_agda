module DASHI.Physics.YangMills.YMClayCMP102OriginalCMP109BishopSeriesSameSourceBIDIExact where

------------------------------------------------------------------------
-- P0 CMP102: SAME original source-defined Bishop A/B represented series.
-- Reuses byte-identical original master CMP109 module at its original path.
-- No duplicate factorials, new limits, Cauchy-product authority or radius.
-- The analytic identity G(X)=0 is NOT declared kernel-proved here.
--
-- Source-written; Agda 2.9 and transitive --safe audit NOT RUN.
-- Original sources: Bałaban CMP102/109, Bishop/Bridges,
-- Murray/Csimma backend, original DASHI finite parity/row owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as P
import Sequence as Seq

import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as CMP109
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102

-- These proofs exploit definitional unfolding of the original source
-- expressions, not a second factorial recursion or numeric matching.
nativeAIsOriginalCMP109A : ∀ n →
  R._≃_ (CMP102.aCoefficient n) (CMP109.aCoefficient n)
nativeAIsOriginalCMP109A n = P.≃-refl

nativeBIsOriginalCMP109B : ∀ n →
  R._≃_ (CMP102.bCoefficient n) (CMP109.bCoefficient n)
nativeBIsOriginalCMP109B n = P.≃-refl

-- One single CMP109 source for the original coefficient series, with
-- precisely the original |X| <= 1/4 hypothesis and represented limits.
-- Normalization is definitional after the two coefficient identities.
nativeASeriesConvergesToOriginalCMP109 :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_
    (Seq.SeriesOf (CMP109.term CMP102.aCoefficient X))
    (CMP109.aSeries X inside)
nativeASeriesConvergesToOriginalCMP109 X inside =
  CMP109.aSeriesConverges X inside

nativeBSeriesConvergesToOriginalCMP109 :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_
    (Seq.SeriesOf (CMP109.term CMP102.bCoefficient X))
    (CMP109.bSeries X inside)
nativeBSeriesConvergesToOriginalCMP109 X inside =
  CMP109.bSeriesConverges X inside

-- Literal historical CMP102 A/B polynomial coefficient constructors
-- at the ORIGINAL CMP109 coefficient source, rather than an independent
-- replacement bracket or shifted finite summation convention.
sourceEvenPart sourceOddPart : Nat → R.ℝ
sourceEvenPart zero = R._*_ CMP102.two (CMP109.aCoefficient zero)
sourceEvenPart (suc n) =
  R._+_
    (R._*_ CMP102.two (CMP109.aCoefficient (suc n)))
    (Row.cauchyCoefficient CMP109.aCoefficient CMP109.aCoefficient n)

sourceOddPart zero = R.1ℝ
sourceOddPart (suc zero) = R._*_ CMP102.two (CMP109.bCoefficient zero)
sourceOddPart (suc (suc n)) =
  R._+_
    (R._*_ CMP102.two (CMP109.bCoefficient (suc n)))
    (Row.cauchyCoefficient CMP109.bCoefficient CMP109.bCoefficient n)

nativeEvenPartIsOriginalCMP109Part : ∀ n →
  R._≃_ (CMP102.evenPart n) (sourceEvenPart n)
nativeEvenPartIsOriginalCMP109Part n = P.≃-refl

nativeOddPartIsOriginalCMP109Part : ∀ n →
  R._≃_ (CMP102.oddPart n) (sourceOddPart n)
nativeOddPartIsOriginalCMP109Part n = P.≃-refl

-- Same literal original coefficient G_n, with the established source
-- finite all-degree proof as its consumer: no analytic conclusion assumed.
sourceBracketCoefficient : Nat → R.ℝ
sourceBracketCoefficient n =
  R._-_ (sourceOddPart n) (sourceEvenPart n)

sourceBracketCoefficientZero : ∀ n →
  R._≃_ (sourceBracketCoefficient n) R.0ℝ
sourceBracketCoefficientZero n =
  CMP102.shiftedNativeBracketCoefficientZero n
