module DASHI.Moonshine.CM163BishopSelectedTauExponentExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- Exact CARTESIAN identity in the ORIGINAL Bishop complex-series carrier:
--   (2*pi_M*i)*((-1+i*sqrt163)/2)
--      = -pi_M*sqrt163 - i*pi_M
-- with the original Machin real and actual selected CM point.
-- The sign of the imaginary part matters: the +i*pi_M exponent is
-- PERIOD-EQUIVALENT but is NOT the literal original 2*pi_M*i*tau.
-- This module is all algebra, no new exp/atan value.

open import Data.Integer.Base using (+_; -_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
open R using (ℝ; _≃_; _*_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.CM163BishopSelectedQScaleTransportExact as Scale
import DASHI.Moonshine.CM163BishopOriginalQPhaseFromCayleyExact as Phase
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Foundations.BishopMachinArctanConstructionExact as M

two : ℝ
two = (+ 2 / 1) ⋆

twoPiImaginary : C.BishopComplex
twoPiImaginary = C.complex R.0ℝ (two * M.bishopMachinPi)

literalExponent : C.BishopComplex
literalExponent = A._*C_ twoPiImaginary CM.tau

signedExponent : C.BishopComplex
signedExponent =
  C.complex (R.- Scale.fullDiskScale) (R.- M.bishopMachinPi)

-- The primitive complex multiplication comes from the already-owned
-- original BishopComplexAlgebraExact, not an alternate model.
literalExponentSigned :
  C._≈C_ literalExponent signedExponent
literalExponentSigned =
  (let open P.ℝ-Solver in
    solve 2 (λ pi r →
      (Κ (+ 0 / 1) ⊗ Κ (- (+ 1) / 2)) ⊖
        ((Κ (+ 2 / 1) ⊗ pi) ⊗ (Κ (+ 1 / 2) ⊗ r))
      ⊜ ⊝ (pi ⊗ r))
      P.≃-refl M.bishopMachinPi N.r) ,
  (let open P.ℝ-Solver in
    solve 2 (λ pi r →
      (Κ (+ 0 / 1) ⊗ (Κ (+ 1 / 2) ⊗ r)) ⊕
        ((Κ (+ 2 / 1) ⊗ pi) ⊗ Κ (- (+ 1) / 2))
      ⊜ ⊝ pi)
      P.≃-refl M.bishopMachinPi N.r)

-- Phase.FromTwoOriginalAtans supplies the exact exponential readout
-- for this exponent on the existing Bishop setoid complex. The
-- correspondence between C and Setoid is Phase.toSeries, same real
-- components; the actual argument is linked by literalExponentSigned.
