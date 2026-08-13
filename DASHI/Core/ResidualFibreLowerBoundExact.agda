module DASHI.Core.ResidualFibreLowerBoundExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- RESIDUAL LOWER BOUNDS AS FIBRE INJECTIVITY
--
-- Cardinality lower bounds reduce constructively to an injection theorem: an
-- exact reopening residual must distinguish every pair of distinct fine states
-- in one quotient fibre.  Likewise, a dynamically sufficient residual must
-- distinguish distinct future-equivalence classes inside one coarse fibre.
------------------------------------------------------------------------

record ExactFibreReopening
    (State Coarse Residual : Set)
    (coarsen : State → Coarse)
    (residual : State → Residual) : Set₁ where
  constructor exactFibreReopening
  field
    reopen : Coarse → Residual → State
    reopenExact :
      (state : State) → reopen (coarsen state) (residual state) ≡ state

open ExactFibreReopening public

exactResidualInjectiveOnEveryFibre :
  ∀ {State Coarse Residual}
    {coarsen : State → Coarse}
    {residual : State → Residual} →
  ExactFibreReopening State Coarse Residual coarsen residual →
  {left right : State} →
  coarsen left ≡ coarsen right →
  residual left ≡ residual right →
  left ≡ right
exactResidualInjectiveOnEveryFibre reopening coarseEqual residualEqual =
  trans
    (sym (reopenExact reopening _))
    (trans
      (cong₂ (reopen reopening) coarseEqual residualEqual)
      (reopenExact reopening _))
  where
    cong₂ :
      ∀ {A B C : Set} (f : A → B → C)
        {a a′ : A} {b b′ : B} →
      a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
    cong₂ f refl refl = refl

sameFibreDistinctStatesForceDistinctResiduals :
  ∀ {State Coarse Residual}
    {coarsen : State → Coarse}
    {residual : State → Residual}
    (reopening : ExactFibreReopening State Coarse Residual coarsen residual)
    {left right : State} →
  coarsen left ≡ coarsen right →
  (left ≡ right → ⊥) →
  residual left ≡ residual right → ⊥
sameFibreDistinctStatesForceDistinctResiduals reopening coarseEqual distinct residualEqual =
  distinct
    (exactResidualInjectiveOnEveryFibre reopening coarseEqual residualEqual)

------------------------------------------------------------------------
-- Dynamic version.  `FutureEq` may be the canonical deterministic,
-- weighted, or probabilistic future equivalence relation.
------------------------------------------------------------------------

record DynamicallySufficientPair
    (State Coarse Residual : Set)
    (FutureEq : State → State → Set)
    (coarsen : State → Coarse)
    (residual : State → Residual) : Set₁ where
  constructor dynamicallySufficientPair
  field
    pairKernelFutureSafe :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      residual left ≡ residual right →
      FutureEq left right

open DynamicallySufficientPair public

distinctFutureClassesForceDistinctResiduals :
  ∀ {State Coarse Residual}
    {FutureEq : State → State → Set}
    {coarsen : State → Coarse}
    {residual : State → Residual}
    (safe : DynamicallySufficientPair
      State Coarse Residual FutureEq coarsen residual)
    {left right : State} →
  coarsen left ≡ coarsen right →
  (FutureEq left right → ⊥) →
  residual left ≡ residual right → ⊥
distinctFutureClassesForceDistinctResiduals safe coarseEqual futureDistinct residualEqual =
  futureDistinct (pairKernelFutureSafe safe coarseEqual residualEqual)

------------------------------------------------------------------------
-- Explicit three-representative lower-bound surface: three pairwise distinct
-- states in one exact quotient fibre require three pairwise distinct residual
-- codes.  This is the constructive content of |D_q| >= 3 without importing a
-- separate finite-cardinality library.
------------------------------------------------------------------------

record ThreeStateFibre
    {State Coarse : Set}
    (coarsen : State → Coarse) : Set₁ where
  constructor threeStateFibre
  field
    first second third : State
    firstSecondSameClass : coarsen first ≡ coarsen second
    firstThirdSameClass : coarsen first ≡ coarsen third
    firstSecondDistinct : first ≡ second → ⊥
    firstThirdDistinct : first ≡ third → ⊥
    secondThirdDistinct : second ≡ third → ⊥

open ThreeStateFibre public

record ThreeResidualCodesDistinct
    {Residual : Set}
    (r₁ r₂ r₃ : Residual) : Set where
  constructor threeResidualCodesDistinct
  field
    firstSecondDifferent : r₁ ≡ r₂ → ⊥
    firstThirdDifferent : r₁ ≡ r₃ → ⊥
    secondThirdDifferent : r₂ ≡ r₃ → ⊥

open ThreeResidualCodesDistinct public

threeStateFibreRequiresThreeDistinctResidualCodes :
  ∀ {State Coarse Residual}
    {coarsen : State → Coarse}
    {residual : State → Residual}
    (reopening : ExactFibreReopening State Coarse Residual coarsen residual)
    (fibre : ThreeStateFibre coarsen) →
  ThreeResidualCodesDistinct
    (residual (first fibre))
    (residual (second fibre))
    (residual (third fibre))
threeStateFibreRequiresThreeDistinctResidualCodes reopening fibre =
  threeResidualCodesDistinct
    (sameFibreDistinctStatesForceDistinctResiduals reopening
      (firstSecondSameClass fibre) (firstSecondDistinct fibre))
    (sameFibreDistinctStatesForceDistinctResiduals reopening
      (firstThirdSameClass fibre) (firstThirdDistinct fibre))
    (sameFibreDistinctStatesForceDistinctResiduals reopening
      (trans (sym (firstSecondSameClass fibre)) (firstThirdSameClass fibre))
      (secondThirdDistinct fibre))
