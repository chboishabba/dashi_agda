module DASHI.Physics.Closure.DirectionalFactorTransportBase where

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; sym)
open import DASHI.MDL.MDLDescentTradeoff
  using (AddMonoid; OrderedMonoid)

----------------------------------------------------------------------
-- Directional factor transport kernel.
--
-- This isolates the exact algebra behind the surviving Gate 2 route:
--
--   transported-ratio = directional-factor * seam-rayleigh-ratio
--
-- and compares it against a coarse lane
--
--   coarse-transport = coarse-factor * seam-rayleigh-ratio.
--
-- If the directional factor is smaller than the coarse factor, then the
-- transported product is smaller as well, provided multiplication is
-- monotone in both arguments.

record DirectionalFactorTransportModel : Set₁ where
  constructor mkDirectionalFactorTransportModel
  field
    orderedMonoid : OrderedMonoid {zero}

  open OrderedMonoid orderedMonoid public
  open AddMonoid M public

  field
    _*_ : N → N → N

    seam-rayleigh-ratio : N
    directional-factor : N
    coarse-factor : N
    transported-ratio : N
    coarse-transport : N

    directionalTransportIdentity :
      transported-ratio ≡
      (directional-factor * seam-rayleigh-ratio)

    coarseTransportIdentity :
      coarse-transport ≡
      (coarse-factor * seam-rayleigh-ratio)

    directionalFactor≤CoarseFactor :
      directional-factor ≤ coarse-factor

    *-mono :
      ∀ a b c d → a ≤ b → c ≤ d → a * c ≤ b * d

  transported≤coarse :
    transported-ratio ≤ coarse-transport
  transported≤coarse =
    subst
      (λ t → transported-ratio ≤ t)
      (sym coarseTransportIdentity)
      (subst
        (λ t → t ≤ (coarse-factor * seam-rayleigh-ratio))
        (sym directionalTransportIdentity)
        (*-mono
          directional-factor
          coarse-factor
          seam-rayleigh-ratio
          seam-rayleigh-ratio
          directionalFactor≤CoarseFactor
          (refl≤ seam-rayleigh-ratio)))

open DirectionalFactorTransportModel public
