module DASHI.Arithmetic.ArithmeticIntegerEmbedding where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_+_; _≤_; _∸_; z≤n)

open import DASHI.TrackedPrimes using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  ; toNat
  ; mapTrackedPrimes15
  )
open import Ontology.GodelLattice using (Vec15)

open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; mkNormalizeAddState
  ; normalizeAddCanonical
  )
open import DASHI.Arithmetic.NormalizeAdd using (normalizeAdd)
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( sum15
  ; primeContribution
  ; primeIndexedPressureAt
  )
open import DASHI.Arithmetic.CancellationPressureFromCanonical using
  ( StateCancellationPressure
  ; StateSupportPressure
  ; normalizeAddOneStepSupportBound
  )
open import DASHI.Arithmetic.VpDepth using
  ( minNat
  ; vp-depth
  )

------------------------------------------------------------------------
-- Minimal concrete integer / valuation carrier.
--
-- This now uses a bounded depth valuation instead of the old 0/1
-- divisibility bit. The depth is fuel-bounded so the arithmetic layer
-- stays total and the bridge shape remains stable.

Int : Set
Int = Nat

add : Int → Int → Int
add = _+_

valuationFuel : Nat
valuationFuel = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

vp : Nat → Int → Nat
vp p n = vp-depth valuationFuel p n

------------------------------------------------------------------------
-- Lanewise integer observations.
--
-- These are the descriptive hooks that feed the 15-lane carrier.

alphaAt : SSP → Int → Int → Nat
alphaAt p x y = vp (toNat p) x

betaAt : SSP → Int → Int → Nat
betaAt p x y = vp (toNat p) y

gammaAt : SSP → Int → Int → Nat
gammaAt p x y = vp (toNat p) (add x y)

deltaAt : SSP → Int → Int → Nat
deltaAt p x y = gammaAt p x y ∸ minNat (alphaAt p x y) (betaAt p x y)

alpha15 : Int → Int → Vec15 Nat
alpha15 x y = mapTrackedPrimes15 (λ p → alphaAt p x y)

beta15 : Int → Int → Vec15 Nat
beta15 x y = mapTrackedPrimes15 (λ p → betaAt p x y)

gamma15 : Int → Int → Vec15 Nat
gamma15 x y = mapTrackedPrimes15 (λ p → gammaAt p x y)

delta15 : Int → Int → Vec15 Nat
delta15 x y = mapTrackedPrimes15 (λ p → deltaAt p x y)

alphaSum : Int → Int → Nat
alphaSum x y = sum15 (alpha15 x y)

betaSum : Int → Int → Nat
betaSum x y = sum15 (beta15 x y)

gammaSum : Int → Int → Nat
gammaSum x y = sum15 (gamma15 x y)

deltaSum : Int → Int → Nat
deltaSum x y = sum15 (delta15 x y)

------------------------------------------------------------------------
-- Embedding into the current NormalizeAddState surface.
--
-- The state is constructed from the local observations. The embed itself is
-- thin and honest: it records the pair, the fixed valuation proxy, and the
-- lanewise summaries.

embed : Int → Int → NormalizeAddState
embed x y =
  mkNormalizeAddState
    zero
    x
    y
    (alphaSum x y)
    (betaSum x y)
    (gammaSum x y)
    (deltaSum x y)
    (minNat (deltaSum x y) (gammaSum x y))
    (delta15 x y)

------------------------------------------------------------------------
-- Direct bridge surfaces.
--
-- These are intentionally narrow. They state how the embedded pair connects
-- to the existing prime-pressure and state-pressure layers without pretending
-- the missing valuation machinery is already proved.

deltaAt-decomposition :
  ∀ p x y →
  deltaAt p x y ≡ gammaAt p x y ∸ minNat (alphaAt p x y) (betaAt p x y)
deltaAt-decomposition _ _ _ = refl

embed-primeContribution :
  ∀ p x y →
  primeContribution p (embed x y) ≡ deltaAt p x y
embed-primeContribution p x y with p
... | p2 = refl
... | p3 = refl
... | p5 = refl
... | p7 = refl
... | p11 = refl
... | p13 = refl
... | p17 = refl
... | p19 = refl
... | p23 = refl
... | p29 = refl
... | p31 = refl
... | p41 = refl
... | p47 = refl
... | p59 = refl
... | p71 = refl

embed-primeIndexedPressure :
  ∀ x y →
  sum15 (primeIndexedPressureAt (embed x y)) ≡ StateCancellationPressure (embed x y)
embed-primeIndexedPressure _ _ = refl

embed-StateCancellationPressure :
  ∀ x y →
  StateCancellationPressure (embed x y) ≡ deltaSum x y
embed-StateCancellationPressure _ _ = refl

embed-StateSupportPressure :
  ∀ x y →
  StateSupportPressure (embed x y) ≡ gammaSum x y
embed-StateSupportPressure _ _ = refl

embed-oneStepSupportBound :
  ∀ x y →
  StateCancellationPressure (normalizeAdd (embed x y)) ≤
  StateSupportPressure (normalizeAdd (embed x y))
embed-oneStepSupportBound x y =
  normalizeAddOneStepSupportBound (embed x y)

------------------------------------------------------------------------
-- Thin packaged surface for downstream consumers.

record ArithmeticIntegerEmbeddingSurface : Set₁ where
  field
    carrier : Set
    embedState : Int → Int → NormalizeAddState
    primeContributionBridge :
      ∀ p x y → primeContribution p (embedState x y) ≡ deltaAt p x y
    primeIndexedBridge :
      ∀ x y →
      sum15 (primeIndexedPressureAt (embedState x y)) ≡
      StateCancellationPressure (embedState x y)
    cancellationPressureBridge :
      ∀ x y →
      StateCancellationPressure (embedState x y) ≡ deltaSum x y
    supportBoundAfterNormalize :
      ∀ x y →
      StateCancellationPressure (normalizeAdd (embedState x y)) ≤
      StateSupportPressure (normalizeAdd (embedState x y))

arithmeticIntegerEmbeddingSurface : ArithmeticIntegerEmbeddingSurface
arithmeticIntegerEmbeddingSurface = record
  { carrier = Int
  ; embedState = embed
  ; primeContributionBridge = embed-primeContribution
  ; primeIndexedBridge = embed-primeIndexedPressure
  ; cancellationPressureBridge = embed-StateCancellationPressure
  ; supportBoundAfterNormalize = embed-oneStepSupportBound
  }
