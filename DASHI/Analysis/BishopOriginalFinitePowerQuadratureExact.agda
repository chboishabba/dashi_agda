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
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as ScaleBridge
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip
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

------------------------------------------------------------------------
-- EXACT NATIVE RATIONAL COEFFICIENT NORMALIZATION.
-- The pinned bishop reciprocalNatRational n is literally 1/(n+1);
-- NatReal.natReal (suc n) is literally n+1. Their cancellation
-- has an existing original proof, not a new order axiom.
------------------------------------------------------------------------

sourceRawPowerQuadratureCell :
  (steps : Nat → R.ℝ) (n j : Nat) → R.ℝ
sourceRawPowerQuadratureCell steps n j =
  R._*_
    (steps j)
    (R.pow (Mesh.sourceVertex steps j) n)

sourceFinitePowerScaledCellIsEmbeddedNat :
  (steps : Nat → R.ℝ) (n j : Nat) →
  R._≃_
    (sourcePowerQuadratureCell steps n j)
    (R._*_
      (NatReal.natReal (suc n))
      (sourceRawPowerQuadratureCell steps n j))
sourceFinitePowerScaledCellIsEmbeddedNat steps n j =
  let
    step = steps j
    power = R.pow (Mesh.sourceVertex steps j) n
    count = NatReal.natReal (suc n)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.*-cong RP.≃-refl
      (ScaleBridge.recursiveScaleIsEmbeddedNaturalMultiply
        (suc n) power))
    (solve 3
      (λ hh cc pp →
        hh ⊗ (cc ⊗ pp)
        ⊜ cc ⊗ (hh ⊗ pp))
      RP.≃-refl step count power)

sourceFinitePowerScaledSumIsEmbeddedNat :
  (steps : Nat → R.ℝ) (n cells : Nat) →
  R._≃_
    (Walk.sumFinite (sourcePowerQuadratureCell steps n) cells)
    (R._*_
      (NatReal.natReal (suc n))
      (Walk.sumFinite (sourceRawPowerQuadratureCell steps n) cells))
sourceFinitePowerScaledSumIsEmbeddedNat steps n zero =
  let open RP.ℝ-Solver in
  solve 1
    (λ cc → Κ 0ℚᵘ ⊜ cc ⊗ Κ 0ℚᵘ)
    RP.≃-refl (NatReal.natReal (suc n))
sourceFinitePowerScaledSumIsEmbeddedNat steps n (suc cells) =
  let
    count = NatReal.natReal (suc n)
    old = Walk.sumFinite (sourceRawPowerQuadratureCell steps n) cells
    next = sourceRawPowerQuadratureCell steps n cells
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (sourceFinitePowerScaledSumIsEmbeddedNat steps n cells)
      (sourceFinitePowerScaledCellIsEmbeddedNat steps n cells))
    (solve 3
      (λ cc oo nn →
        (cc ⊗ oo) ⊕ (cc ⊗ nn)
        ⊜ cc ⊗ (oo ⊕ nn))
      RP.≃-refl count old next)

originalFinitePowerQuadratureEndpointReciprocalBound :
  (steps : Nat → R.ℝ) (power cells : Nat) →
  (vertexNN : (j : Nat) →
    R.NonNegative (Mesh.sourceVertex steps j)) →
  (stepNN : (j : Nat) → R.NonNegative (steps j)) →
  let
    reciprocal = R._⋆ (Recip.reciprocalNatRational power)
    endpoint = R._-_
      (R.pow (Mesh.sourceVertex steps cells) (suc power))
      (R.pow (Mesh.sourceVertex steps zero) (suc power))
  in
  R._≤_
    (Walk.sumFinite (sourceRawPowerQuadratureCell steps power) cells)
    (R._*_ reciprocal endpoint)
originalFinitePowerQuadratureEndpointReciprocalBound
    steps power cells vertexNN stepNN =
  let
    count = NatReal.natReal (suc power)
    reciprocal = R._⋆ (Recip.reciprocalNatRational power)
    rawSum = Walk.sumFinite (sourceRawPowerQuadratureCell steps power) cells
    endpoint = R._-_
      (R.pow (Mesh.sourceVertex steps cells) (suc power))
      (R.pow (Mesh.sourceVertex steps zero) (suc power))
    scaleBound = RP.≤-respˡ-≃
      (RP.≃-symm
        (sourceFinitePowerScaledSumIsEmbeddedNat steps power cells))
      (originalFinitePowerQuadratureEndpointBound
        steps power cells vertexNN stepNN)
    multiplied = RP.*-monoˡ-≤-nonNeg
      scaleBound
      (Recip.reciprocalNonnegative power)
    cancel = Recip.embeddedReciprocalNatCancels power
    open RP.ℝ-Solver
    leftNormal =
      RP.≃-trans
        (solve 3
          (λ rr cc ss →
            rr ⊗ (cc ⊗ ss)
            ⊜ (rr ⊗ cc) ⊗ ss)
          RP.≃-refl reciprocal count rawSum)
        (RP.≃-trans
          (RP.*-cong cancel RP.≃-refl)
          (RP.*-identityˡ rawSum))
  in
  RP.≤-respˡ-≃ (RP.≃-symm leftNormal) multiplied
