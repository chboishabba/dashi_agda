module DASHI.MDL.MDLDescentTradeoff where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

-- Minimal ordered commutative monoid interface.
record AddMonoid {ℓ} : Set (suc ℓ) where
  field
    N   : Set ℓ
    _+_ : N → N → N
    0#  : N

open AddMonoid public

record OrderedMonoid {ℓ} : Set (suc ℓ) where
  field
    M    : AddMonoid {ℓ}
    _≤_  : N M → N M → Set ℓ
    refl≤  : ∀ x → x ≤ x
    trans≤ : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    mono+  : ∀ a b c d → a ≤ b → c ≤ d →
      _≤_ (AddMonoid._+_ M a c) (AddMonoid._+_ M b d)

open OrderedMonoid public

record MDLParts {ℓx ℓn}
  (X : Set ℓx) (O : OrderedMonoid {ℓn})
  : Set (suc (ℓx ⊔ ℓn)) where
  open AddMonoid (M O)
  field
    P D T : X → X
    ModelLen ResidLen : X → AddMonoid.N (M O)
    MDL : X → AddMonoid.N (M O)
    MDL-def : ∀ x → MDL x ≡ AddMonoid._+_ (M O) (ModelLen (P x)) (ResidLen (D x))

open MDLParts public

record TradeoffLemma {ℓx ℓn}
  {X : Set ℓx} {O : OrderedMonoid {ℓn}}
  (Parts : MDLParts X O)
  : Set (suc (ℓx ⊔ ℓn)) where
  open OrderedMonoid O
  open AddMonoid (M O)
  field
    model-drop : ∀ x →
      OrderedMonoid._≤_ O
        (ModelLen Parts (P Parts (T Parts x)))
        (ModelLen Parts (P Parts x))
    resid-drop : ∀ x →
      OrderedMonoid._≤_ O
        (ResidLen Parts (D Parts (T Parts x)))
        (ResidLen Parts (D Parts x))

open TradeoffLemma public

-- Descent theorem from the single tradeoff seam.
--
-- Empirical learning (LHC harness): monotone descent holds strongly for
-- L1/MDL-proxy energies even when raw χ² is non-contractive. This matches
-- the intended geometry: Fejér/closest-point descent to a fixed set,
-- not global Euclidean contraction. Keep the seam here; do not assume
-- strict contraction in the raw metric.
MDLDescent :
  ∀ {ℓx ℓn} {X : Set ℓx} {O : OrderedMonoid {ℓn}}
  (Parts : MDLParts X O)
  (L : TradeoffLemma Parts)
  → ∀ x → OrderedMonoid._≤_ O (MDL Parts (T Parts x)) (MDL Parts x)
MDLDescent {O = O} Parts L x =
  let
    open OrderedMonoid O
    open AddMonoid (M O)
    open TradeoffLemma L
    mdlt : MDL Parts (T Parts x) ≡
      AddMonoid._+_ (M O)
        (ModelLen Parts (P Parts (T Parts x)))
        (ResidLen Parts (D Parts (T Parts x)))
    mdlt = MDL-def Parts (T Parts x)
    mdlx : MDL Parts x ≡
      AddMonoid._+_ (M O)
        (ModelLen Parts (P Parts x))
        (ResidLen Parts (D Parts x))
    mdlx = MDL-def Parts x
    step : OrderedMonoid._≤_ O
      (AddMonoid._+_ (M O)
        (ModelLen Parts (P Parts (T Parts x)))
        (ResidLen Parts (D Parts (T Parts x))))
      (AddMonoid._+_ (M O)
        (ModelLen Parts (P Parts x))
        (ResidLen Parts (D Parts x)))
    step = OrderedMonoid.mono+ O
      (ModelLen Parts (P Parts (T Parts x)))
      (ModelLen Parts (P Parts x))
      (ResidLen Parts (D Parts (T Parts x)))
      (ResidLen Parts (D Parts x))
      (TradeoffLemma.model-drop L x)
      (TradeoffLemma.resid-drop L x)
  in
  subst
    (λ v → OrderedMonoid._≤_ O v (MDL Parts x))
    (sym mdlt)
    (subst
      (λ v → OrderedMonoid._≤_ O
        (AddMonoid._+_ (M O)
          (ModelLen Parts (P Parts (T Parts x)))
          (ResidLen Parts (D Parts (T Parts x))))
        v)
      (sym mdlx)
      step)
