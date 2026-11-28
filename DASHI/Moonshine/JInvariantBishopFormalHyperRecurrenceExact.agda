module DASHI.Moonshine.JInvariantBishopFormalHyperRecurrenceExact where

-- SOURCE-WRITTEN, UNCOMPILED. Transport the original factorial
-- recurrence to the literal composed coefficients. Finite support,
-- rather than an analytic derivative or an assumed composition law.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _⋆)
import RealProperties as P
import Data.Nat.Properties as NP
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as W
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopFormalCompositionFlowExact as F
import DASHI.Moonshine.JInvariantBishopFiniteCompositionExchangeExact as EX
import DASHI.Moonshine.JInvariantBishopFormalGeometricInverseExact as I
open G
open U using (X3; Y2; disc)
open H using (Zcoord; unitSeries; zeroSeries; power; compose; weightedCoeff)
open F using (C; finiteCompose; composePrefix; composeOuterCong)

finiteShift : (c b : Series) (N : Nat) →
  finiteCompose c b (suc N) ≈s
  (constant (c zero) ⊕s (b ⊗s finiteCompose (Row.shift c) b N))
finiteShift c b zero =
  transS (λ n → P.+-identityˡ (scale (c zero) unitSeries n))
    (transS (symS (constantScale (c zero) unitSeries))
      (transS (W.rowUnitRight (constant (c zero)))
        (symS (transS (addCong reflS (H.zeroRow b))
          (λ n → P.+-identityʳ (constant (c zero) n))))))
finiteShift c b (suc N) =
  transS (addCong (finiteShift c b N) (symS (W.rowScaleRight (c (suc N)) b (power b N))))
    (transS (let open G.Solver in
      solve 3 (λ a b c → (a ⊕ b) ⊕ c ⊜ a ⊕ (b ⊕ c)) reflS
        (constant (c zero)) (b ⊗s finiteCompose (Row.shift c) b N)
        (b ⊗s scale (c (suc N)) (power b N)))
      (addCong reflS (symS (W.rowAddRight b
        (finiteCompose (Row.shift c) b N) (scale (c (suc N)) (power b N))))))

composeShift : (c b : Series) → b zero ≃ R.0ℝ →
  compose c b ≈s (constant (c zero) ⊕s (b ⊗s compose (Row.shift c) b))
composeShift c b hb n =
  P.≃-trans
    (P.≃-symm (P.≃-trans (P.+-cong P.≃-refl
      (U.right0 (H.powerBelow b hb (suc n) n (NP.n<1+n n))))
      (P.+-identityʳ (compose c b n))))
    (P.≃-trans (finiteShift c b (suc n) n)
      (P.+-cong P.≃-refl (P.≃-symm (U.convPrefix b (compose (Row.shift c) b)
        (finiteCompose (Row.shift c) b (suc n)) n (composePrefix (Row.shift c) b hb n)))))

finiteAdd : (a c b : Series) (N : Nat) →
  finiteCompose (a ⊕s c) b N ≈s (finiteCompose a b N ⊕s finiteCompose c b N)
finiteAdd a c b zero n = P.≃-symm (P.+-identityʳ R.0ℝ)
finiteAdd a c b (suc N) n =
  P.≃-trans (P.+-cong (finiteAdd a c b N n)
    (P.*-distribʳ-+ (power b N n) (a N) (c N)))
    (let open P.ℝ-Solver in
      solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d))
        P.≃-refl (finiteCompose a b N n) (finiteCompose c b N n)
        (R._*_ (a N) (power b N n)) (R._*_ (c N) (power b N n)))

finiteScale : (a : ℝ) (c b : Series) (N : Nat) →
  finiteCompose (scale a c) b N ≈s scale a (finiteCompose c b N)
finiteScale a c b zero n = P.≃-symm (P.*-zeroʳ a)
finiteScale a c b (suc N) n =
  P.≃-trans (P.+-cong (finiteScale a c b N n)
    (P.*-assoc a (c N) (power b N n)))
    (P.≃-symm (P.*-distribˡ-+ a (finiteCompose c b N n) (R._*_ (c N) (power b N n))))

composeAdd : (a c b : Series) → compose (a ⊕s c) b ≈s (compose a b ⊕s compose c b)
composeAdd a c b n = finiteAdd a c b (suc n) n

composeScale : (a : ℝ) (c b : Series) → compose (scale a c) b ≈s scale a (compose c b)
composeScale a c b n = finiteScale a c b (suc n) n

rhsOuter : Series
rhsOuter = scale ((+ 3 / 2) ⋆) (weightedCoeff 2) ⊕s
  scale ((+ 23 / 36) ⋆) (weightedCoeff 1) ⊕s scale ((+ 5 / 72) ⋆) (weightedCoeff zero)

rhs : Series
rhs = scale ((+ 3 / 2) ⋆) (C 2) ⊕s
  scale ((+ 23 / 36) ⋆) (C 1) ⊕s scale ((+ 5 / 72) ⋆) (C zero)

outerODE : Row.shift (weightedCoeff 3) ≈s (weightedCoeff 3 ⊕s rhsOuter)
outerODE n = P.≃-trans (H.unweightedODE n)
  (let open P.ℝ-Solver in
    solve 4 (λ a b c d → a ⊕ b ⊕ c ⊕ d ⊜ a ⊕ (b ⊕ c ⊕ d))
      P.≃-refl (weightedCoeff 3 n) (scale ((+ 3 / 2) ⋆) (weightedCoeff 2) n)
      (scale ((+ 23 / 36) ⋆) (weightedCoeff 1) n) (scale ((+ 5 / 72) ⋆) (weightedCoeff zero) n))

rhsCompose : compose rhsOuter Zcoord ≈s rhs
rhsCompose =
  transS (composeAdd (scale ((+ 3 / 2) ⋆) (weightedCoeff 2) ⊕s
    scale ((+ 23 / 36) ⋆) (weightedCoeff 1)) (scale ((+ 5 / 72) ⋆) (weightedCoeff zero)) Zcoord)
    (transS (addCong (composeAdd (scale ((+ 3 / 2) ⋆) (weightedCoeff 2))
      (scale ((+ 23 / 36) ⋆) (weightedCoeff 1)) Zcoord) reflS)
      (addCong (addCong (composeScale ((+ 3 / 2) ⋆) (weightedCoeff 2) Zcoord)
        (composeScale ((+ 23 / 36) ⋆) (weightedCoeff 1) Zcoord))
        (composeScale ((+ 5 / 72) ⋆) (weightedCoeff zero) Zcoord)))

shiftCompose : compose (Row.shift (weightedCoeff 3)) Zcoord ≈s (C 3 ⊕s rhs)
shiftCompose =
  transS (composeOuterCong (Row.shift (weightedCoeff 3)) (weightedCoeff 3 ⊕s rhsOuter) Zcoord outerODE)
    (transS (composeAdd (weightedCoeff 3) rhsOuter Zcoord) (addCong reflS rhsCompose))

outer3Zero : weightedCoeff 3 zero ≃ R.0ℝ
outer3Zero = let open P.ℝ-Solver in
  solve 1 (λ h → (((Κ 1ℚᵘ ⊗ Κ 0ℚᵘ) ⊗ Κ 0ℚᵘ) ⊗ Κ 0ℚᵘ) ⊗ h ⊜ Κ 0ℚᵘ)
    P.≃-refl (H.hyperCoeff zero)

actualHyperRecurrence : C 3 ≈s (Zcoord ⊗s (C 3 ⊕s rhs))
actualHyperRecurrence =
  transS (composeShift (weightedCoeff 3) Zcoord H.zCoordZero)
    (transS (addCong (constantCong outer3Zero) (mulCong reflS shiftCompose))
      (λ n → P.+-identityˡ ((Zcoord ⊗s (C 3 ⊕s rhs)) n)))

-- Cancel only the already-proved formal denominator X^3.
-- The signed cusp degree remains zero on both sides.
clearedHyperRecurrence : (Y2 ⊗s C 3) ≈s (disc ⊗s rhs)
clearedHyperRecurrence =
  let
    h : (X3 ⊗s C 3) ≈s (disc ⊗s (C 3 ⊕s rhs))
    h = transS (mulCong reflS actualHyperRecurrence)
      (transS (symS (W.rowAssoc X3 Zcoord (C 3 ⊕s rhs)))
        (mulCong I.actualZDenominator reflS))
    open G.Solver
  in transS
    (solve 3 (λ x y f → y ⊗ f ⊜ x ⊗ f ⊖ (x ⊖ y) ⊗ f)
      reflS X3 Y2 (C 3))
    (transS (subCong h reflS)
      (solve 3 (λ d f r → d ⊗ (f ⊕ r) ⊖ d ⊗ f ⊜ d ⊗ r) reflS disc (C 3) rhs))
