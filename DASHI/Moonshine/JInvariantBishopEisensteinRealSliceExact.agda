module DASHI.Moonshine.JInvariantBishopEisensteinRealSliceExact where

-- SOURCE-WRITTEN, not kernel checked. Actual completed E4/E6 and
-- proof-relevant Klein j are real whenever the original q is real.
-- No separate real-valued modular function or complex norm is introduced.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_)
import Real as R
import RealProperties as P
import Sequence as S
import Inverse as Inv
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopNativeProofRelevantKleinExact as K
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext

RealSlice : C.BishopComplex → Set
RealSlice z = R._≃_ (C.im z) R.0ℝ

zeroReal : RealSlice A.zeroC
zeroReal = P.≃-refl

oneReal : RealSlice A.oneC
oneReal = P.≃-refl

zeroPlusZero : R._≃_ (R._+_ R.0ℝ R.0ℝ) R.0ℝ
zeroPlusZero = P.+-identityʳ R.0ℝ

zeroNeg : R._≃_ (R.- R.0ℝ) R.0ℝ
zeroNeg =
  let open P.ℝ-Solver in
  solve 0 (⊝ (Κ (+ 0 / 1)) ⊜ Κ (+ 0 / 1)) P.≃-refl

addReal : ∀ {x y} → RealSlice x → RealSlice y →
  RealSlice (A._+C_ x y)
addReal {C.complex a b} {C.complex c d} x y =
  P.≃-trans (P.+-cong x y) zeroPlusZero

subReal : ∀ {x y} → RealSlice x → RealSlice y →
  RealSlice (A._-C_ x y)
subReal {C.complex a b} {C.complex c d} x y =
  P.≃-trans
    (P.+-cong x (P.≃-trans (P.-‿cong y) zeroNeg))
    zeroPlusZero

scaleReal : ∀ {z} → (s : R.ℝ) → RealSlice z →
  RealSlice (A.scaleC s z)
scaleReal {C.complex a b} s h =
  P.≃-trans (P.*-cong P.≃-refl h) (P.*-zeroʳ s)

mulReal : ∀ {x y} → RealSlice x → RealSlice y →
  RealSlice (A._*C_ x y)
mulReal {C.complex a b} {C.complex c d} x y =
  P.≃-trans
    (P.+-cong
      (P.≃-trans (P.*-cong P.≃-refl y) (P.*-zeroʳ a))
      (P.≃-trans (P.*-cong x P.≃-refl) (P.*-zeroˡ c)))
    zeroPlusZero

powReal : ∀ {q} → RealSlice q → (n : Nat) →
  RealSlice (A.powC q n)
powReal h zero = oneReal
powReal h (suc n) = mulReal h (powReal h n)

conjugateReal : ∀ {z} → RealSlice z → RealSlice (Rec.conjugateC z)
conjugateReal {C.complex a b} h =
  P.≃-trans (P.-‿cong h) zeroNeg

reciprocalReal : ∀ {z} → (nz : Rec.BishopComplexNonzero z) →
  RealSlice z → RealSlice (Rec.reciprocalC z nz)
reciprocalReal {z} nz h =
  scaleReal (Inv._⁻¹ (Norm.normSqC z) (Rec.normSquareNonzero nz))
    (conjugateReal h)

zeroTerms : Nat → R.ℝ
zeroTerms _ = R.0ℝ

zeroPartial : (n : Nat) → R._≃_ (S.SeriesOf zeroTerms n) R.0ℝ
zeroPartial zero = P.≃-refl
zeroPartial (suc n) = P.≃-trans (P.+-cong (zeroPartial n) P.≃-refl) zeroPlusZero

zeroSeriesConverges : S._ConvergesTo_ (S.SeriesOf zeroTerms) R.0ℝ
zeroSeriesConverges = S.xₙ≃c⇒xₙ→c (λ {(suc n) → zeroPartial (suc n)})

realSeriesLimit : ∀ {terms : Nat → C.BishopComplex} {v} →
  ((n : Nat) → RealSlice (terms n)) →
  C.ComplexSeriesConvergesTo terms v → RealSlice v
realSeriesLimit h conv =
  Ext.termwiseEquivalentSeriesHaveEquivalentLimits
    h (C.imagConverges conv) zeroSeriesConverges

module AtDisk {q : C.BishopComplex} {r : R.ℝ}
  (input : Disk.BishopUnitDiskQ q r) (realQ : RealSlice q) where

  module Actual = K.AtDisk input

  e4TailReal : RealSlice (E.e4BishopTailLimit q (Disk.unitInterval input)
    (Disk.powerEnvelope input))
  e4TailReal =
    realSeriesLimit
      (λ n → scaleReal (E.e4CoefficientReal n) (powReal realQ (suc n)))
      (Disk.e4Converges Actual.completion)

  e6UnsignedTailReal : RealSlice (E.e6BishopUnsignedTailLimit q
    (Disk.unitInterval input) (Disk.powerEnvelope input))
  e6UnsignedTailReal =
    realSeriesLimit
      (λ n → scaleReal (E.e6CoefficientReal n) (powReal realQ (suc n)))
      (Disk.e6Converges Actual.completion)

  e4Real : RealSlice Actual.E4
  e4Real = addReal oneReal e4TailReal

  e6Real : RealSlice Actual.E6
  e6Real = subReal oneReal e6UnsignedTailReal

  cubeReal : ∀ {z} → RealSlice z → RealSlice (K.cube z)
  cubeReal h = mulReal (mulReal h h) h

  deltaReal : RealSlice Actual.Delta
  deltaReal =
    scaleReal (R._⋆ (+ 1 / 1728))
      (subReal (cubeReal e4Real) (mulReal e6Real e6Real))

  jReal : (negative : R._<_ (C.re Actual.Delta) R.0ℝ) →
    RealSlice (Actual.jFromNegativeDelta negative)
  jReal negative =
    mulReal (cubeReal e4Real)
      (reciprocalReal (Actual.negativeDeltaWitness negative) deltaReal)
