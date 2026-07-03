module DASHI.Physics.Closure.ExactKNAOperatorTransferBase where

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; sym; trans)
open import DASHI.Physics.Closure.QuotientAwareLiftDefectExpansionBase
  using (QuotientAwareLiftDefectExpansionModel)

----------------------------------------------------------------------
-- Exact Gate 2 operator-transfer kernel.
--
-- This is the first genuinely nonlocal algebraic theorem after the
-- seam-local quotient-aware transport model.  It isolates the exact
-- identities that are still missing on the true carrier:
--
--   1. a Schur-linearity identity identifying the seam transported ratio
--      with the quotient-aware transport quantity; and
--   2. an exact restriction identity identifying the true K_N(A) ratio
--      with that seam-transported ratio.
--
-- The live route is extremizer-aware rather than worst-case:
--
--   seam-transported-ratio
--     ≤ directional-transport-factor * seam-rayleigh-ratio
--
-- on the near-extremizer cone, and the product budget is then closed under
-- the conservative quarter threshold.
--
-- Once these identities and the directional product bound are supplied on
-- the actual carrier, the quarter bound transfers to the exact normalized
-- leakage operator.

record ExactKNAOperatorTransferModel : Set₁ where
  constructor mkExactKNAOperatorTransferModel
  field
    quotientAwareModel : QuotientAwareLiftDefectExpansionModel

  open QuotientAwareLiftDefectExpansionModel quotientAwareModel public

  field
    _*_ : N → N → N

    seam-transported-ratio : N
    exact-kna-ratio : N
    seam-rayleigh-ratio : N
    directional-transport-factor : N

    schurLinearityTransfer :
      seam-transported-ratio ≡ transported-ratio

    exactRestrictionIdentity :
      exact-kna-ratio ≡ seam-transported-ratio

    directionalTransportBound :
      seam-transported-ratio ≤
      (directional-transport-factor * seam-rayleigh-ratio)

    subcriticalDirectionalBudget :
      (directional-transport-factor * seam-rayleigh-ratio) ≤ one-quarter

  seamTransported≤quarter : seam-transported-ratio ≤ one-quarter
  seamTransported≤quarter =
    subst
      (λ t → t ≤ one-quarter)
      (sym schurLinearityTransfer)
      transported≤quarter

  seamTransported≤quarter-viaDirectional :
    seam-transported-ratio ≤ one-quarter
  seamTransported≤quarter-viaDirectional =
    trans≤
      seam-transported-ratio
      (directional-transport-factor * seam-rayleigh-ratio)
      one-quarter
      directionalTransportBound
      subcriticalDirectionalBudget

  exactTransportIdentity :
    exact-kna-ratio ≡ transported-ratio
  exactTransportIdentity =
    trans exactRestrictionIdentity schurLinearityTransfer

  exactKNA≤quarter : exact-kna-ratio ≤ one-quarter
  exactKNA≤quarter =
    subst
      (λ t → t ≤ one-quarter)
      (sym exactTransportIdentity)
      transported≤quarter

  exactKNA≤quarter-viaDirectional : exact-kna-ratio ≤ one-quarter
  exactKNA≤quarter-viaDirectional =
    subst
      (λ t → t ≤ one-quarter)
      (sym exactRestrictionIdentity)
      seamTransported≤quarter-viaDirectional

open ExactKNAOperatorTransferModel public
