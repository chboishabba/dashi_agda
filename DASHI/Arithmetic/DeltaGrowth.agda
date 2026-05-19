module DASHI.Arithmetic.DeltaGrowth where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (NonZero)
open import Data.Nat using (_≤_; _∸_; z≤n; s≤s; _^_; _/_)
open import Data.Nat.Divisibility using
  ( _∣_
  ; 1∣_
  ; _∣?_
  ; ∣⇒≤
  ; ∣-trans
  ; *-monoʳ-∣
  ; *-monoˡ-∣
  ; m∣n/o⇒o*m∣n
  )
open import Data.Nat.Divisibility.Core using (divides)
open import Data.Nat.Properties as NatP using
  ( ≤-refl
  ; ≤-trans
  ; ^-monoʳ-≤
  ; m∸n≤m
  ; *-comm
  ; *-assoc
  )
open import Relation.Nullary.Decidable.Core using (yes; no)

open import MonsterOntos using (SSP; toNat)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; valuationFuel
  ; gammaAt
  ; deltaAt
  )
open import DASHI.Arithmetic.VpDepth using
  ( vp-depth
  ; minNat
  )

------------------------------------------------------------------------
-- Arithmetic growth frontier.
--
-- The first real arithmetic cap is divisibility:
--
--   p ^ δ_p ∣ x + y
--
-- For the current bounded valuation this is constructive. The size
-- inequality then follows for nonzero sums using `∣⇒≤`.

pow : Nat → Nat → Nat
pow = _^_

------------------------------------------------------------------------
-- Power divisibility for the bounded depth valuation itself.

pow-mono-divides :
  ∀ p m n →
  m ≤ n →
  pow p m ∣ pow p n
pow-mono-divides p zero n _ = 1∣ _
pow-mono-divides p (suc m) (suc n) (s≤s m≤n) =
  *-monoʳ-∣ p (pow-mono-divides p m n m≤n)

vp-depth-power-divides :
  ∀ fuel p n →
  pow p (vp-depth fuel p n) ∣ n
vp-depth-power-divides zero p n = 1∣ n
vp-depth-power-divides (suc fuel) zero n = 1∣ n
vp-depth-power-divides (suc fuel) (suc zero) n = 1∣ n
vp-depth-power-divides (suc fuel) (suc (suc p)) n with suc (suc p) ∣? n
... | no _ = 1∣ n
... | yes p∣n =
  let
    q-divides : pow (suc (suc p)) (vp-depth fuel (suc (suc p)) (n / suc (suc p))) ∣ (n / suc (suc p))
    q-divides =
      vp-depth-power-divides fuel (suc (suc p)) (n / suc (suc p))
  in
  m∣n/o⇒o*m∣n p∣n q-divides

------------------------------------------------------------------------
-- Delta-level divisibility and the resulting nonzero size bound.

deltaPowerDividesSum :
  ∀ p x y →
  pow (toNat p) (deltaAt p x y) ∣ (x + y)
deltaPowerDividesSum p x y =
  ∣-trans
    (pow-mono-divides
      (toNat p)
      (deltaAt p x y)
      (gammaAt p x y)
      (≤-trans
        (m∸n≤m (gammaAt p x y) (minNat (vp-depth valuationFuel (toNat p) x) (vp-depth valuationFuel (toNat p) y)))
        ≤-refl))
    (vp-depth-power-divides valuationFuel (toNat p) (x + y))

deltaPower≤sum :
  ∀ p x y →
  .{{_ : NonZero (x + y)}} →
  pow (toNat p) (deltaAt p x y) ≤ x + y
deltaPower≤sum p x y = ∣⇒≤ (deltaPowerDividesSum p x y)

------------------------------------------------------------------------
-- Logarithmic corollary remains the explicit frontier.
--
-- The divisibility/size step is now constructive. The remaining open gap is
-- whatever logarithm interface we want to expose on top of Nat.

postulate
  logNat : Nat → Nat

  deltaGrowthBound :
    ∀ p x y →
    .{{_ : NonZero (x + y)}} →
    deltaAt p x y * logNat (toNat p) ≤ logNat (x + y)

record DeltaGrowthStructure : Set₁ where
  field
    logarithm : Nat → Nat
    power : Nat → Nat → Nat
    powerDivides :
      ∀ p x y →
      power (toNat p) (deltaAt p x y) ∣ x + y
    powerBound :
      ∀ p x y →
      .{{_ : NonZero (x + y)}} →
      power (toNat p) (deltaAt p x y) ≤ x + y
    logBound :
      ∀ p x y →
      .{{_ : NonZero (x + y)}} →
      deltaAt p x y * logarithm (toNat p) ≤ logarithm (x + y)

open DeltaGrowthStructure public

deltaGrowthStructure : DeltaGrowthStructure
deltaGrowthStructure = record
  { logarithm = logNat
  ; power = pow
  ; powerDivides = deltaPowerDividesSum
  ; powerBound = deltaPower≤sum
  ; logBound = deltaGrowthBound
  }
