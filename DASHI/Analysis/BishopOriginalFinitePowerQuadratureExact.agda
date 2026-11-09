module DASHI.Analysis.BishopOriginalFinitePowerQuadratureExact where

------------------------------------------------------------------------
-- P0.06 precursor: ORIGINAL BISHOP FINITE POWER QUADRATURE.
--
-- For source nonnegative endpoints x and y=x+h with h>=0:
--
--   h * (suc n) * x^n <= y^(suc n)-x^(suc n).
--
-- We do NOT divide by h. The original powerDifferenceQuotient
-- obeys q(x,h,suc n) = q(x,0,suc n)+h*T(x,h,suc n);
-- positivity of h and T gives q(x,0)<=q(x,h).
--
-- For ANY finite original walk of nonnegative ascending vertices,
-- summing these local estimates yields the exact endpoint:
--
--   sum_{j<m} h_j * (suc n) * v_j^n
--       <= (v_m)^(suc n) - (v_0)^(suc n).
--
-- The Nat-scale (suc n) is the ALREADY PROVED source natScale.
-- Conversion to 1/(suc n) uses the existing Bishop Nat
-- reciprocal cancellation owner; not a new integral/FTC axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopOriginalFiniteLogSecondQuotientPositiveExact as Positive
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Scale
import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh

sourcePowerSecantAtLeastDerivative :
  (x h : R.ℝ) (n : Nat) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (hNN : R.NonNegative h) →
  R._≤_
    (Power.powerDifferenceQuotient x R.0ℝ (suc n))
    (Power.powerDifferenceQuotient x h (suc n))
sourcePowerSecantAtLeastDerivative x h n xNN yNN hNN =
  let
    q0 = Power.powerDifferenceQuotient x R.0ℝ (suc n)
    tq = Second.sourcePowerSecondQuotient x h (suc n)
    excessNN = RP.nonNegx,y⇒nonNegx*y hNN
      (Positive.originalPowerSecondQuotientNonnegative
        x h xNN yNN (suc n))
    oldBelowExtended =
      RP.≤-respˡ-≃
        (RP.≃-symm (RP.+-identityʳ q0))
        (RP.+-monoʳ-≤ q0
          (RP.nonNegx⇒0≤x excessNN))
  in
  RP.≤-respʳ-≃
    (RP.≃-symm
      (Second.originalPowerQuotientSecondOrder x h (suc n)))
    oldBelowExtended

originalFinitePowerLowerQuadratureCell :
  (x h : R.ℝ) (n : Nat) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (hNN : R.NonNegative h) →
  R._≤_
    (R._*_ h (Scale.natScale (suc n) (R.pow x n)))
    (R._-_
      (R.pow (R._+_ x h) (suc n))
      (R.pow x (suc n)))
originalFinitePowerLowerQuadratureCell x h n xNN yNN hNN =
  let
    q0 = Power.powerDifferenceQuotient x R.0ℝ (suc n)
    qh = Power.powerDifferenceQuotient x h (suc n)
    byMonotonicity = RP.*-monoˡ-≤-nonNeg
      (sourcePowerSecantAtLeastDerivative x h n xNN yNN hNN)
      hNN
  in
  RP.≤-respʳ-≃
    (RP.≃-symm (Power.powerDifferenceFactorisation x h (suc n)))
    (RP.≤-respˡ-≃
      (RP.*-cong RP.≃-refl
        (RP.≃-symm (Power.quotientAtZero x n)))
      byMonotonicity)

-- The original source summand uses only one actual finiteWalk.
sourcePowerQuadratureCell :
  (steps : Nat → R.ℝ) (n j : Nat) → R.ℝ
sourcePowerQuadratureCell steps n j =
  R._*_
    (steps j)
    (Scale.natScale (suc n)
      (R.pow (Mesh.sourceVertex steps j) n))

-- No separate selected sum: this is exactly the finiteWalk
-- original sumFinite recursion used for the original log-ODE.
originalFinitePowerQuadratureEndpointBound :
  (steps : Nat → R.ℝ) (power cells : Nat) →
  (vertexNN : (j : Nat) →
    R.NonNegative (Mesh.sourceVertex steps j)) →
  (stepNN : (j : Nat) → R.NonNegative (steps j)) →
  R._≤_
    (Walk.sumFinite
      (sourcePowerQuadratureCell steps power) cells)
    (R._-_
      (R.pow (Mesh.sourceVertex steps cells) (suc power))
      (R.pow (Mesh.sourceVertex steps zero) (suc power)))
originalFinitePowerQuadratureEndpointBound
    steps power zero vertexNN stepNN =
  let
    initial = R.pow (Mesh.sourceVertex steps zero) (suc power)
  in
  RP.≤-respʳ-≃
    (RP.≃-symm (RP.+-inverseʳ initial))
    RP.≤-refl
originalFinitePowerQuadratureEndpointBound
    steps power (suc cells) vertexNN stepNN =
  let
    v = Mesh.sourceVertex steps cells
    next = Mesh.sourceVertex steps (suc cells)
    old = R.pow v (suc power)
    last = R.pow next (suc power)
    initial = R.pow (Mesh.sourceVertex steps zero) (suc power)
    local = originalFinitePowerLowerQuadratureCell
      v (steps cells) power
      (vertexNN cells) (vertexNN (suc cells))
      (stepNN cells)
    inductive =
      RP.+-mono-≤
        (originalFinitePowerQuadratureEndpointBound
          steps power cells vertexNN stepNN)
        local
    open RP.ℝ-Solver
    telescope =
      solve 3
        (λ first current after →
          (current ⊖ first) ⊕ (after ⊖ current)
          ⊜ after ⊖ first)
        RP.≃-refl initial old last
  in
  RP.≤-respʳ-≃ telescope inductive
