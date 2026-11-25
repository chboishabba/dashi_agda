module DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact where

-- SOURCE-WRITTEN, UNCOMPILED. The literal negative-real CM q chart,
-- using the original Machin real, canonical sqrt(163) and native exp.
-- No assumed q value or arbitrary disk input in the downstream forms.
-- Equality with the actual complex exponential at tau remains separate.
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
open import Data.Nat.Base using (s≤s; z≤n)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as N
import DASHI.Foundations.BishopNatSquareRootPositiveExact as RootPos
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as MP
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopEisensteinRealSliceExact as Slice
import DASHI.Moonshine.JInvariantBishopCM163RealSlicePeriodExact as CM
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Norm
import DASHI.Foundations.BishopChudnovskyNativeEulerLimitsExact as Euler
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as End

half : ℝ
half = (+ 1 / 2) ⋆

imag : ℝ
imag = half * Norm.r

imagPositive : R._<_ R.0ℝ imag
imagPositive = P.posx⇒0<x
  (P.posx,y⇒posx*y
    (P.posp⇒posp⋆ (+ 1 / 2) (QP.positive⁻¹ (+ 1 / 2)))
    (RootPos.canonicalFloorSquareRootPositive (s≤s z≤n)))

tau : C.BishopComplex
tau = C.complex (((Z.-_ (+ 1)) / 2) ⋆) imag

radius : ℝ
radius = Radius.machinQRadius imag

-- q at the real-negative chart. Retain the minus sign and zero im.
q : C.BishopComplex
q = C.complex (R.- radius) R.0ℝ

qReal : Slice.RealSlice q
qReal = P.≃-refl

qNorm : N.normSqC q ≃ N.square radius
qNorm = let open P.ℝ-Solver in
  solve 1 (λ r → (⊝ r) ⊗ (⊝ r) ⊕ Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ ⊜ r ⊗ r)
    P.≃-refl radius

input : Disk.BishopUnitDiskQ q radius
input = record
  { Disk.unitInterval = Radius.machinQRadiusUnitInterval imagPositive
  ; Disk.normSquareAgreement = qNorm
  }

module Selected = CM.AtDisk input qReal

-- Both E4/E6 and all their original q-series limits are constructed
-- without a separate caller-supplied convergence or disk witness.
-- Only the literal discriminant sign, CM root, and analytic Euler/Hecke
-- source identities remain. The CM q phase equivalence is not inferred
-- merely from this negative-real coordinate construction.
periodFromSelectedRootAndJet :
  (negative : R._<_ Selected.d R.0ℝ) →
  (e : ℝ) → R.Positive Selected.X →
  let module V = Selected.AtNegativeDelta negative in
  V.j ≃ CM.negC →
  Norm.sq Euler.H ≃ Selected.X →
  (Norm.six * Selected.Y * Euler.J₁) ≃
    (Euler.H * (e * Selected.X - Selected.Y)) →
  ((M.bishopMachinPi * Norm.r) *
    (Norm.B * Selected.X * e - Norm.D * Selected.Y)) ≃
    (Norm.six * Norm.B * Selected.X) →
  End.NativePeriod
periodFromSelectedRootAndJet negative e px hj hf he hc =
  Selected.AtNegativeDelta.periodFromRootAndSignedJet negative e px hj hf he hc
