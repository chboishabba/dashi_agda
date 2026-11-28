module DASHI.Moonshine.CM163BishopSelectedQScaleTransportExact where

-- SOURCE-WRITTEN / KERNEL PENDING. Same ORIGINAL Bishop selected CM q.
-- Coarse -> fine: the actual radius exponent and the signed disk
-- logarithmic scale are the SAME number. The tau displacement scale
-- pi*Im(tau) is half of this number. No foreign/trigonometric pi,
-- no new complex exponential identity, and no fabricated q-phase.

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
open R using (ℝ; _≃_; _*_; _⋆)
import RealProperties as P
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as Selected
import DASHI.Moonshine.JInvariantBishopCM163RadiusGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Tail
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as Reduction
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Norm

-- Actual tau=(-1+i sqrt163)/2 and the original Machin real.
tauHalfScale : ℝ
tauHalfScale = Machin.bishopMachinPi * Selected.imag

two : ℝ
two = (+ 2 / 1) ⋆

-- The source readout is the same p used by the original disk jet.
fullDiskScale : ℝ
fullDiskScale = Reduction.p

-- The exponential radius exponent is 2 pi Im(tau) exactly.
qRadiusExponent : ℝ
qRadiusExponent = Radius.qExponentMagnitude
  Machin.bishopMachinPi Selected.imag

-- No cancellation and no division: pure signed polynomial transport.
halfToFull : (two * tauHalfScale) ≃ fullDiskScale
halfToFull = let open P.ℝ-Solver in
  solve 2 (λ pi r →
    Κ (+ 2 / 1) ⊗ (pi ⊗ (Κ (+ 1 / 2) ⊗ r))
    ⊜ pi ⊗ r)
    P.≃-refl Machin.bishopMachinPi Norm.r

exponentToDisk : qRadiusExponent ≃ fullDiskScale
exponentToDisk = let open P.ℝ-Solver in
  solve 2 (λ pi r →
    (Κ (+ 2 / 1) ⊗ pi) ⊗ (Κ (+ 1 / 2) ⊗ r)
    ⊜ pi ⊗ r)
    P.≃-refl Machin.bishopMachinPi Norm.r

-- Round-trip equivalence is explicit, not hidden in a rewritten parameter.
diskToHalf : fullDiskScale ≃ (two * tauHalfScale)
diskToHalf = P.≃-symm halfToFull

radiusToDisk : Guard.exponent ≃ fullDiskScale
radiusToDisk = Guard.exponentShape

diskToRadius : fullDiskScale ≃ Guard.exponent
diskToRadius = P.≃-symm radiusToDisk

-- The selected point and real-slice guard are already constructed.
selectedNegativeDelta : R._<_ Selected.Selected.d R.0ℝ
selectedNegativeDelta = Tail.negativeDelta

selectedE4Positive : R.Positive Selected.Selected.X
selectedE4Positive = Tail.xPositive

selectedE6Positive : R.Positive Selected.Selected.Y
selectedE6Positive = Tail.yPositive

-- These imply the original guarded j exists. Its exact CM value,
-- however, still requires actual Hecke/modular rigidity.
module OriginalRoot = Tail.Root

-- Phase boundary (not assumed here):
-- The required analytic source theorem is an equality between the
-- original Bishop complex exponential q(tau), evaluated at Selected.tau,
-- and Selected.q = complex(-exp(-fullDiskScale),0).
-- An equality with a legacy trigonometric pi or its complex exponent
-- does NOT inhabit that Bishop original-source proposition.
