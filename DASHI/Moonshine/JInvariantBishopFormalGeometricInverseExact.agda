module DASHI.Moonshine.JInvariantBishopFormalGeometricInverseExact where

-- SOURCE-WRITTEN, UNCOMPILED. Finite power telescoping on the literal
-- formal Cauchy row. The only padding is the already-proved zero support.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NP
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_≃_)
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as W
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopFiniteCompositionExchangeExact as EX
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
open G

powerAdd : (b : Series) (j k : Nat) →
  H.power b (j + k) ≈s (H.power b j ⊗s H.power b k)
powerAdd b zero k = symS (W.rowUnitLeft (H.power b k))
powerAdd b (suc j) k =
  transS (mulCong reflS (powerAdd b j k))
    (symS (W.rowAssoc b (H.power b j) (H.power b k)))

geo : Series → Nat → Series
geo b N n = R.∑₀ (λ k → H.power b k n) N

geoTelescoping : (b : Series) (N : Nat) →
  ((H.unitSeries ⊖s b) ⊗s geo b N) ≈s
  (H.unitSeries ⊖s H.power b N)
geoTelescoping b zero =
  let open G.Solver in
  solve 1 (λ b → (Κ 1ℚᵘ ⊖ b) ⊗ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ ⊖ Κ 1ℚᵘ)
    reflS b
geoTelescoping b (suc N) =
  transS (W.rowAddRight (H.unitSeries ⊖s b) (geo b N) (H.power b N))
    (transS (addCong (geoTelescoping b N) reflS)
      (let open G.Solver in
       solve 2 (λ b p → (Κ 1ℚᵘ ⊖ p) ⊕ ((Κ 1ℚᵘ ⊖ b) ⊗ p)
         ⊜ Κ 1ℚᵘ ⊖ b ⊗ p) reflS b (H.power b N)))

geometric : Series → Series
geometric b = H.compose (λ _ → R.1ℝ) b

geometricAt : (b : Series) (j : Nat) →
  geometric b j ≃ geo b (suc j) j
geometricAt b j =
  EX.sumPrefix (λ k → R._*_ R.1ℝ (H.power b k j))
    (λ k → H.power b k j) (suc j)
    (λ k _ → P.*-identityˡ (H.power b k j))

geometricPrefix : (b : Series) → b zero ≃ R.0ℝ →
  (n : Nat) → U.PrefixEq (geometric b) (geo b (suc n)) n
geometricPrefix b hb n j hj =
  P.≃-trans (geometricAt b j)
    (P.≃-symm (EX.pad (λ k → H.power b k j) (suc j) (suc n)
      (Data.Nat.Base.s≤s hj) (λ k hk → H.powerBelow b hb k j hk)))

inverseFromZeroMode : (b : Series) → b zero ≃ R.0ℝ →
  ((H.unitSeries ⊖s b) ⊗s geometric b) ≈s H.unitSeries
inverseFromZeroMode b hb n =
  P.≃-trans (U.convPrefix (H.unitSeries ⊖s b) (geometric b)
    (geo b (suc n)) n (geometricPrefix b hb n))
    (P.≃-trans (geoTelescoping b (suc n) n)
      (P.≃-trans (P.+-cong P.≃-refl
        (P.-‿cong (H.powerBelow b hb (suc n) n (NP.n<1+n n))))
        (let open P.ℝ-Solver in
          solve 1 (λ a → a ⊖ Κ 0ℚᵘ ⊜ a) P.≃-refl (H.unitSeries n))))

x3AsOneMinus : (H.unitSeries ⊖s H.minusX3Tail) ≈s U.X3
x3AsOneMinus n =
  let open P.ℝ-Solver in
  solve 2 (λ u x → u ⊖ (⊝ Κ 1ℚᵘ) ⊗ (x ⊖ u) ⊜ x)
    P.≃-refl (H.unitSeries n) (U.X3 n)

actualInverseX3 : (U.X3 ⊗s H.inverseX3) ≈s H.unitSeries
actualInverseX3 =
  transS (mulCong (symS x3AsOneMinus) reflS)
    (inverseFromZeroMode H.minusX3Tail H.inverseInnerZero)

actualZDenominator : (U.X3 ⊗s H.Zcoord) ≈s U.disc
actualZDenominator =
  transS (let open G.Solver in
    solve 3 (λ x d i → x ⊗ (d ⊗ i) ⊜ d ⊗ (x ⊗ i))
      reflS U.X3 U.disc H.inverseX3)
    (transS (mulCong reflS actualInverseX3) (W.rowUnitRight U.disc))
