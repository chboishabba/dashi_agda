module DASHI.Moonshine.JInvariantBishopFormalCompositionFlowExact where

-- SOURCE-WRITTEN, UNCOMPILED. Transport the actual Euler flow through
-- finite zero-supported composition. No analytic chain rule, inverse
-- of q, or shifted-power division. All sums are literal Bishop sums.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (s≤s)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _*_; _⋆)
import RealProperties as P
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as W
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopFormalZFlowExact as Z
import DASHI.Moonshine.JInvariantBishopFiniteCompositionExchangeExact as EX
open G
open F using (δ; dAdd; dMul; RamanujanX; RamanujanY)
open U using (X; Y)
open H using (Zcoord; unitSeries; zeroSeries; power; compose)

dUnit : δ unitSeries ≈s zeroSeries
dUnit zero = U.D0 unitSeries
dUnit (suc n) = P.*-zeroʳ (R.pow (NR.natReal (suc n)) 1)

dZero : δ zeroSeries ≈s zeroSeries
dZero n = P.*-zeroʳ (R.pow (NR.natReal n) 1)

dScaleReal : (c : ℝ) (p : Series) →
  δ (scale c p) ≈s scale c (δ p)
dScaleReal c p n = let open P.ℝ-Solver in
  solve 3 (λ d c p → d ⊗ (c ⊗ p) ⊜ c ⊗ (d ⊗ p))
    P.≃-refl (R.pow (NR.natReal n) 1) c (p n)

-- Multiply the derivative by x before transporting the power.
-- The proof is division-free and keeps the k=0 mode.
powerFlow : (x y b : Series) → (x ⊗s δ b) ≈s (y ⊗s b) →
  (k : Nat) → (x ⊗s δ (power b k)) ≈s scale (NR.natReal k) (y ⊗s power b k)
powerFlow x y b h zero =
  transS (mulCong reflS dUnit)
    (transS (H.zeroRow x)
      (symS (λ n → P.*-zeroˡ ((y ⊗s unitSeries) n))))
powerFlow x y b h (suc k) =
  let p = power b k
      K = NR.natReal k
  in transS (mulCong reflS (dMul b p))
    (transS (let open G.Solver in
      solve 5 (λ x b p db dp → x ⊗ (db ⊗ p ⊕ b ⊗ dp)
        ⊜ (x ⊗ db) ⊗ p ⊕ b ⊗ (x ⊗ dp))
        reflS x b p (δ b) (δ p))
      (transS (addCong (mulCong h reflS) (mulCong reflS (powerFlow x y b h k)))
        (transS (addCong reflS (mulCong reflS (symS (constantScale K (y ⊗s p)))))
          (transS (let open G.Solver in
            solve 4 (λ y b p K → (y ⊗ b) ⊗ p ⊕ b ⊗ (K ⊗ (y ⊗ p))
              ⊜ (K ⊕ Κ 1ℚᵘ) ⊗ (y ⊗ (b ⊗ p)))
              reflS y b p (constant K))
            (transS (mulCong (transS (symS (constantAdd K R.1ℝ))
              (constantCong (P.≃-symm (NR.natRealSuccessor k)))) reflS)
              (constantScale (NR.natReal (suc k)) (y ⊗s power b (suc k))))))))

weightedOuter : Series → Series
weightedOuter c k = NR.natReal k * c k

finiteCompose : Series → Series → Nat → Series
finiteCompose c b N n = R.∑₀ (λ k → c k * power b k n) N

composePrefix : (c b : Series) → b zero ≃ R.0ℝ →
  (n : Nat) → U.PrefixEq (compose c b) (finiteCompose c b (suc n)) n
composePrefix c b hz n j hj =
  P.≃-symm (EX.pad (λ k → c k * power b k j) (suc j) (suc n)
    (s≤s hj) (λ k hk → U.right0 (H.powerBelow b hz k j hk)))

scaledPowerFlow : (x y b c : Series) →
  (x ⊗s δ b) ≈s (y ⊗s b) → (k : Nat) →
  (x ⊗s δ (scale (c k) (power b k))) ≈s
    (y ⊗s scale (weightedOuter c k) (power b k))
scaledPowerFlow x y b c h k =
  let p = power b k
  in transS (mulCong reflS (dScaleReal (c k) p))
    (transS (W.rowScaleRight (c k) x (δ p))
      (transS (λ n → P.*-congˡ (powerFlow x y b h k n))
        (transS (λ n → let open P.ℝ-Solver in
          solve 3 (λ c k p → c ⊗ (k ⊗ p) ⊜ (k ⊗ c) ⊗ p)
            P.≃-refl (c k) (NR.natReal k) ((y ⊗s p) n))
          (symS (W.rowScaleRight (weightedOuter c k) y p)))))

finiteFlow : (x y b c : Series) → (x ⊗s δ b) ≈s (y ⊗s b) →
  (N : Nat) →
  (x ⊗s δ (finiteCompose c b N)) ≈s
    (y ⊗s finiteCompose (weightedOuter c) b N)
finiteFlow x y b c h zero =
  transS (mulCong reflS dZero) (transS (H.zeroRow x) (symS (H.zeroRow y)))
finiteFlow x y b c h (suc N) =
  transS (mulCong reflS (dAdd (finiteCompose c b N) (scale (c N) (power b N))))
    (transS (W.rowAddRight x (δ (finiteCompose c b N)) (δ (scale (c N) (power b N))))
      (transS (addCong (finiteFlow x y b c h N) (scaledPowerFlow x y b c h N))
        (symS (W.rowAddRight y (finiteCompose (weightedOuter c) b N)
          (scale (weightedOuter c N) (power b N))))))

compositionFlow : (x y b c : Series) → b zero ≃ R.0ℝ →
  (x ⊗s δ b) ≈s (y ⊗s b) →
  (x ⊗s δ (compose c b)) ≈s (y ⊗s compose (weightedOuter c) b)
compositionFlow x y b c hz h n =
  P.≃-trans (U.convPrefix x (δ (compose c b)) (δ (finiteCompose c b (suc n))) n
    (U.Dprefix 1 (composePrefix c b hz n)))
    (P.≃-trans (finiteFlow x y b c h (suc n) n)
      (P.≃-symm (U.convPrefix y (compose (weightedOuter c) b)
        (finiteCompose (weightedOuter c) b (suc n)) n
        (composePrefix (weightedOuter c) b hz n))))

-- The selected outer stream is the ORIGINAL signed factorial source
-- unweighted by the fixed CM coordinate, not another hypergeometric.
C : Nat → Series
C d = compose (H.weightedCoeff d) Zcoord

outerStep : (d k : Nat) → weightedOuter (H.weightedCoeff d) k ≃ H.weightedCoeff (suc d) k
outerStep d k = let open P.ℝ-Solver in
  solve 3 (λ k p h → k ⊗ (p ⊗ h) ⊜ (p ⊗ k) ⊗ h)
    P.≃-refl (NR.natReal k) (R.pow (NR.natReal k) d) (H.hyperCoeff k)

composeOuterCong : (c e b : Series) → c ≈s e → compose c b ≈s compose e b
composeOuterCong c e b h n = EX.sumPrefix
  (λ k → c k * power b k n) (λ k → e k * power b k n) (suc n)
  (λ k hk → P.*-congʳ (h k))

actualChain : RamanujanX → RamanujanY → (d : Nat) →
  (X ⊗s δ (C d)) ≈s (Y ⊗s C (suc d))
actualChain hx hy d =
  transS (compositionFlow X Y Zcoord (H.weightedCoeff d) H.zCoordZero (Z.actualZFlow hx hy))
    (mulCong reflS (composeOuterCong (weightedOuter (H.weightedCoeff d))
      (H.weightedCoeff (suc d)) Zcoord (outerStep d)))
