module DASHI.Analysis.RiemannHermitianIntrospectiveRoundTripExact where

------------------------------------------------------------------------
-- INTROSPECTIVE ROUND-TRIP
--
-- This module records theorem consequences recovered by rendering the current
-- Hermitian-defect implementation as a deterministic geometric proof and then
-- inspecting that rendering.
--
-- IMPORTANT AUTHORITY BOUNDARY
-- The visualization is not evidence for new analytic zeta facts.  It is only
-- an observer on algebra already present in:
--
--   * RiemannCenteredGridRetentionExact
--   * RiemannWeilPairKernelFrobeniusExact
--   * RiemannG3SourceTransportExact
--
-- The recovered statements below are proved again from those formal objects.
-- No pixel fact is promoted directly to mathematical authority.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)

open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Solver as IntSolver using ()
open IntSolver.+-*-Solver using (solve; _:*_; _:+_; _:-_; con; _:=_)
  renaming (solve to solveℤ; _:*_ to _:*ℤ_; _:+_ to _:+ℤ_; _:-_ to _:-ℤ_; con to conℤ; _:=_ to _:=ℤ_)

open import DASHI.Analysis.RiemannCenteredGridRetentionExact
open import DASHI.Analysis.RiemannWeilPairKernelFrobeniusExact

------------------------------------------------------------------------
-- FINDING 1: CANONICAL QUARTER-RETENTION IDENTITY
--
-- The existing centered-grid certificate says
--
--   B_full = 4 B_tail + 2 M
--   B_fin  = B_tail + M.
--
-- The visual stacked-bar observer makes the common tail pieces immediate:
--
--   B_full + 2 M = 4 B_fin.
--
-- Thus the finite one-sided source grid retains at least one quarter of the
-- full symmetric transverse energy, with the exact excess above one quarter
-- measured by 2M.  We state this subtraction-free, so it remains constructive.
------------------------------------------------------------------------

quarterRetentionIdentity :
  (g : CenteredImaginaryGridLedger) →
  (c : CenteredFiniteRetentionCertificate g) →
  fullImaginaryEnergy g + 2 * margin c
    ≡ 4 * finitePositiveImaginaryEnergy g
quarterRetentionIdentity g c
  rewrite fullEnergyAsFourTailPlusTwoMargin c
        | finiteEnergyAsTailPlusMargin c =
  solve 2
    (λ t m →
      ((con 4 :* t) :+ (con 2 :* m)) :+ (con 2 :* m)
        := con 4 :* (t :+ m))
    refl
    (tailEnergy c) (margin c)

record QuarterRetentionCertificate
  (g : CenteredImaginaryGridLedger) : Set where
  constructor quarterRetentionCertificate
  field
    finiteQuarterSlack : Nat
    fullPlusSlackIsFourFinite :
      fullImaginaryEnergy g + finiteQuarterSlack
        ≡ 4 * finitePositiveImaginaryEnergy g

open QuarterRetentionCertificate public

centeredRetentionImpliesQuarterRetention :
  (g : CenteredImaginaryGridLedger) →
  CenteredFiniteRetentionCertificate g →
  QuarterRetentionCertificate g
centeredRetentionImpliesQuarterRetention g c =
  quarterRetentionCertificate
    (2 * margin c)
    (quarterRetentionIdentity g c)

centeredTailDominationImpliesQuarterRetention :
  (g : CenteredImaginaryGridLedger) →
  CenteredGridTailDomination g →
  QuarterRetentionCertificate g
centeredTailDominationImpliesQuarterRetention g h =
  centeredRetentionImpliesQuarterRetention g
    (centeredTailDominationImpliesRetention g h)

------------------------------------------------------------------------
-- FINDING 2: THE S/H CHANNEL MAP HAS AN EXACT INTEGER INVERSE UP TO SCALE 2
--
-- Existing definitions:
--
--   Im S = q + r
--   Im H = r - q
--
-- with q = a.d and r = b.c.
--
-- The visual proof displays these as the two 45-degree axes.  Inspection makes
-- clear that this is a Hadamard transform, not a quotient.  Algebraically:
--
--   Im S - Im H = 2 q
--   Im S + Im H = 2 r.
--
-- Together with the already-proved Parseval identity
--
--   (Im S)^2 + (Im H)^2 = 2(q^2+r^2),
--
-- this shows the complex difference/sum kernels retain the complete mixed
-- two-channel information up to the integral scale factor 2.
------------------------------------------------------------------------

holomorphicMinusHermitianImagRecoversTwiceAD :
  (x : PairCrossMoments) →
  holomorphicImag x - hermitianImag x
    ≡ (+ 2) * ad x
holomorphicMinusHermitianImagRecoversTwiceAD
  (pairCrossMoments p q r s) =
  solveℤ 2
    (λ q r →
      (q :+ℤ r) :-ℤ (r :-ℤ q)
        :=ℤ conℤ (+ 2) :*ℤ q)
    refl
    q r

holomorphicPlusHermitianImagRecoversTwiceBC :
  (x : PairCrossMoments) →
  holomorphicImag x + hermitianImag x
    ≡ (+ 2) * bc x
holomorphicPlusHermitianImagRecoversTwiceBC
  (pairCrossMoments p q r s) =
  solveℤ 2
    (λ q r →
      (q :+ℤ r) :+ℤ (r :-ℤ q)
        :=ℤ conℤ (+ 2) :*ℤ r)
    refl
    q r

record HadamardMixedChannelRecovery (x : PairCrossMoments) : Set where
  constructor hadamardMixedChannelRecovery
  field
    recoverTwiceAD :
      holomorphicImag x - hermitianImag x ≡ (+ 2) * ad x
    recoverTwiceBC :
      holomorphicImag x + hermitianImag x ≡ (+ 2) * bc x
    preserveMixedEnergy :
      imaginaryKernelEnergy x
        ≡ (+ 2) * mixedChannelInterferenceEnergy x

open HadamardMixedChannelRecovery public

mixedChannelsHaveHadamardRecovery :
  (x : PairCrossMoments) → HadamardMixedChannelRecovery x
mixedChannelsHaveHadamardRecovery x =
  hadamardMixedChannelRecovery
    (holomorphicMinusHermitianImagRecoversTwiceAD x)
    (holomorphicPlusHermitianImagRecoversTwiceBC x)
    (imaginaryKernelEnergyIsTwiceMixedInterference x)

------------------------------------------------------------------------
-- INTROSPECTIVE CONCLUSION
--
-- The visualization did not close a new analytic zeta gap.  It refined the
-- shape of two existing gaps:
--
-- G1 finite retention can target a quantitative quarter-retention certificate
-- rather than merely nonvanishing finite energy.
--
-- G2 complex kernel control is information-complete for the two mixed channels
-- (up to scale 2), so no separate hidden vector observable is required once the
-- S/H kernels have been analytically identified.
------------------------------------------------------------------------
