module DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact where

-- SOURCE-WRITTEN, kernel pending. Instantiate the actual cyclic norm
-- and formal Euler identity on the original Ramanujan J coefficients.
-- No fitted polynomial, external log series, or arbitrary phase stream.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (refl; _≡_)
open import Data.Nat.DivMod using (_%_; _/_)
import Data.Nat.Properties as NP
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Rational.Unnormalised using (ℚᵘ; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_⋆; _≃_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as Euler
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open G using (Series; _⊗s_; _⊖s_; _⊕s_; scale)
open N using (SeriesC; _≈cs_; _⊗c_)

J : Series
J = D.Junit

J0 : J zero ≃ R.1ℝ
J0 = P.≃-trans (U.mul0 {f = U.X3} {g = D.reciprocal} U.x30 D.reciprocal0) U.unitMul

expand : Series → Series
expand f n with n % 41 NP.≟ zero
... | yes _ = f (n / 41)
... | no _ = R.0ℝ

expand0 : ∀ f → expand f zero ≃ f zero
expand0 f = P.≃-refl

-- Shift by literal nonnegative degree, with exact zero padding.
delay : Nat → Series → Series
delay zero f n = f n
delay (suc k) f zero = R.0ℝ
delay (suc k) f (suc n) = delay k f n

t41 : Series
t41 = delay 41 H.unitSeries

hDiag hSlice gDiag gSlice : Series
hDiag = expand J ⊖s delay 40 J
hSlice = J ⊖s delay 1 (G.constant (Shift.Kq ⋆))
gDiag = delay 1640 (expand J) ⊖s expand (expand J)
gSlice = expand (expand J) ⊖s delay 1681 (G.constant (Shift.Kq ⋆))

hDiag0 : hDiag zero ≃ R.1ℝ
hDiag0 = P.≃-trans (P.+-cong J0 P.≃-refl)
  (let open P.ℝ-Solver in solve 0 (Κ 1ℚᵘ ⊖ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ) P.≃-refl)

hSlice0 : hSlice zero ≃ R.1ℝ
hSlice0 = P.≃-trans (P.+-cong J0 P.≃-refl)
  (let open P.ℝ-Solver in solve 0 (Κ 1ℚᵘ ⊖ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ) P.≃-refl)

-- The original descending packet c0..cd has normalized value
-- sum c_k t^(41*k) J(t^41)^(d-k). Horner retains its exact degree.
column : List ℚᵘ → Series
column [] = H.zeroSeries
column (c ∷ cs) =
  scale (c ⋆) (H.power (expand J) (length cs)) ⊕s (t41 ⊗s column cs)

diagColumn sliceColumn : Series
diagColumn = column Packet.diagonal
sliceColumn = column Packet.slice

module At (inputs : Round11.BishopCutset) where
  module Norm = N.At inputs
  module E = Euler.At inputs

  diagNorm sliceNorm : SeriesC
  diagNorm = Norm.norm (Euler.lift hDiag)
  sliceNorm = Norm.norm (Euler.lift hSlice)

  diagEuler : Euler.δ diagNorm ≈cs
    (E.traceFrom (Euler.lift (Euler.Log.ell hDiag hDiag0)) zero 41 ⊗c diagNorm)
  diagEuler = E.actualNormFlow hDiag hDiag0

  sliceEuler : Euler.δ sliceNorm ≈cs
    (E.traceFrom (Euler.lift (Euler.Log.ell hSlice hSlice0)) zero 41 ⊗c sliceNorm)
  sliceEuler = E.actualNormFlow hSlice hSlice0

  diagOffSector : ∀ n → (n % 41 ≡ zero → ⊥) → C._≈C_ (diagNorm n) A.zeroC
  diagOffSector = Norm.offSector (Euler.lift hDiag)
  sliceOffSector : ∀ n → (n % 41 ≡ zero → ⊥) → C._≈C_ (sliceNorm n) A.zeroC
  sliceOffSector = Norm.offSector (Euler.lift hSlice)

  diagonalNormalized sliceNormalized : SeriesC
  diagonalNormalized = Euler.lift gDiag ⊗c diagNorm
  sliceNormalized = Euler.lift gSlice ⊗c sliceNorm

  -- Exact formal residuals of the ORIGINAL packet. The all-degree
  -- analytic evaluation and finite prefix reflection remain separate.
  diagonalResidual sliceResidual : SeriesC
  diagonalResidual n = A._-C_ (diagonalNormalized n) (Euler.lift diagColumn n)
  sliceResidual n = A._-C_ (sliceNormalized n) (Euler.lift sliceColumn n)
