module DASHI.Analysis.RiemannAristotleProjectiveBalanceStrictBudgetNoGoExact where

------------------------------------------------------------------------
-- PROJECTIVE-BALANCE NO-GO
--
-- If the literal projective balance identifies the surviving cluster margin
-- with the surviving off-ordinate post-Schur energy, then a strict inequality
-- placing that same energy below that same margin is impossible.
--
-- This is deliberately generic order algebra.  It prevents a downstream
-- budget compiler from hiding an inconsistent strict-margin hypothesis.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

record StrictBalanceSurface : Set₁ where
  constructor strict-balance-surface
  field
    Scalar : Set
    _<_ : Scalar → Scalar → Set
    ltIrreflexive : ∀ x → x < x → ⊥

open StrictBalanceSurface public

strictBelowImpossibleUnderBalance :
  (S : StrictBalanceSurface) →
  (offEnergy clusterMargin : Scalar S) →
  offEnergy ≡ clusterMargin →
  offEnergy < clusterMargin →
  ⊥
strictBelowImpossibleUnderBalance S offEnergy .offEnergy refl hlt =
  ltIrreflexive S offEnergy hlt

record ProjectiveBalanceStrictBudgetBoundary : Set where
  constructor projective-balance-strict-budget-boundary
  field
    literalBalanceStrictBudgetNoGoClosedInAgda : Bool
    literalBalanceStrictBudgetNoGoClosedInAgdaIsTrue :
      literalBalanceStrictBudgetNoGoClosedInAgda ≡ true

    checkedLeanBalanceNoGoExists : Bool
    checkedLeanBalanceNoGoExistsIsTrue :
      checkedLeanBalanceNoGoExists ≡ true

    strictBudgetUnderUnbrokenBalanceAdmissible : Bool
    strictBudgetUnderUnbrokenBalanceAdmissibleIsFalse :
      strictBudgetUnderUnbrokenBalanceAdmissible ≡ false

    balanceBreakingPremiseRequiredForStrictContradictionRoute : Bool
    balanceBreakingPremiseRequiredForStrictContradictionRouteIsTrue :
      balanceBreakingPremiseRequiredForStrictContradictionRoute ≡ true

canonicalProjectiveBalanceStrictBudgetBoundary :
  ProjectiveBalanceStrictBudgetBoundary
canonicalProjectiveBalanceStrictBudgetBoundary =
  projective-balance-strict-budget-boundary
    true refl
    true refl
    false refl
    true refl
