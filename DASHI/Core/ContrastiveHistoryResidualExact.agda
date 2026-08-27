module DASHI.Core.ContrastiveHistoryResidualExact where

------------------------------------------------------------------------
-- CONTRASTIVE HISTORY RESIDUAL
--
-- A generic observer seam for systems in which the action-relevant extra
-- information is not simply a stored historical state, but a comparison
-- between retained history and the current observation.
--
--   state -> current observation
--         -> history observation
--         -> contrast(history,current)
--
-- The module deliberately separates three questions:
--
--   * does contrast refine current-only observation?
--   * can contrast be reconstructed from current observation alone?
--   * is (current,contrast) sufficient for a particular downstream action?
--
-- The last obligation is explicit: a useful contrastive residual need not be a
-- complete decision state.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

ContrastiveResidual :
  ∀ {State History Present Contrast : Set} →
  (State → History) →
  (State → Present) →
  (History → Present → Contrast) →
  State → Contrast
ContrastiveResidual history present contrast state =
  contrast (history state) (present state)

currentAndContrastObserver :
  ∀ {State History Present Contrast : Set} →
  (State → History) →
  (State → Present) →
  (History → Present → Contrast) →
  Observer.Observer State (Present × Contrast)
currentAndContrastObserver history present contrast =
  Observer.pairObserver present (ContrastiveResidual history present contrast)

contrastiveCollisionGivesStrictRefinement :
  ∀ {State History Present Contrast : Set}
    (history : State → History)
    (present : State → Present)
    (contrast : History → Present → Contrast)
    (x y : State) →
  present x ≡ present y →
  (ContrastiveResidual history present contrast x
    ≡ ContrastiveResidual history present contrast y → ⊥) →
  Observer.StrictRefinement
    present
    (currentAndContrastObserver history present contrast)
contrastiveCollisionGivesStrictRefinement history present contrast x y samePresent differentContrast =
  Observer.strictPairRefinement
    present
    (ContrastiveResidual history present contrast)
    x y samePresent differentContrast

ContrastDescendsThroughCurrent :
  ∀ {State History Present Contrast : Set} →
  (State → History) →
  (State → Present) →
  (History → Present → Contrast) →
  Set
ContrastDescendsThroughCurrent {Present = Present} {Contrast = Contrast}
  history present contrast =
  Σ (Present → Contrast)
    (λ reconstruct →
      ∀ state →
      reconstruct (present state)
      ≡ ContrastiveResidual history present contrast state)

contrastiveCollisionBlocksCurrentDescent :
  ∀ {State History Present Contrast : Set}
    {history : State → History}
    {present : State → Present}
    {contrast : History → Present → Contrast}
    {x y : State} →
  present x ≡ present y →
  (ContrastiveResidual history present contrast x
    ≡ ContrastiveResidual history present contrast y → ⊥) →
  ContrastDescendsThroughCurrent history present contrast →
  ⊥
contrastiveCollisionBlocksCurrentDescent {x = x} {y = y} samePresent differentContrast descent =
  differentContrast
    (trans
      (sym (commutes x))
      (trans
        (cong reconstruct samePresent)
        (commutes y)))
  where
    reconstruct = proj₁ descent
    commutes = proj₂ descent

------------------------------------------------------------------------
-- Downstream sufficiency is a separate commuting-square obligation.
------------------------------------------------------------------------

record ContrastSufficientFor
    {State History Present Contrast Action : Set}
    (history : State → History)
    (present : State → Present)
    (contrast : History → Present → Contrast)
    (action : State → Action) : Set where
  constructor contrastSufficientFor
  field
    quotientAction : Present × Contrast → Action
    factorization :
      ∀ state →
      quotientAction
        (present state , ContrastiveResidual history present contrast state)
      ≡ action state

open ContrastSufficientFor public

sameCurrentContrastDifferentActionBlocksSufficiency :
  ∀ {State History Present Contrast Action : Set}
    {history : State → History}
    {present : State → Present}
    {contrast : History → Present → Contrast}
    {action : State → Action}
    {x y : State} →
  present x ≡ present y →
  ContrastiveResidual history present contrast x
    ≡ ContrastiveResidual history present contrast y →
  (action x ≡ action y → ⊥) →
  ContrastSufficientFor history present contrast action →
  ⊥
sameCurrentContrastDifferentActionBlocksSufficiency {x = x} {y = y}
  samePresent sameContrast differentAction sufficient =
  differentAction
    (trans
      (sym (factorization sufficient x))
      (trans
        (cong (quotientAction sufficient) pairSame)
        (factorization sufficient y)))
  where
    pairSame :
      (present x , ContrastiveResidual history present contrast x)
      ≡
      (present y , ContrastiveResidual history present contrast y)
    pairSame rewrite samePresent | sameContrast = refl

record ContrastiveHistoryBoundary : Set where
  constructor contrastiveHistoryBoundary
  field
    relationalResidualRepresentable : Bool
    relationalResidualRepresentableIsTrue :
      relationalResidualRepresentable ≡ true

    contrastCanStrictlyRefineCurrentObservation : Bool
    contrastCanStrictlyRefineCurrentObservationIsTrue :
      contrastCanStrictlyRefineCurrentObservation ≡ true

    currentObservationAutomaticallyDeterminesContrast : Bool
    currentObservationAutomaticallyDeterminesContrastIsFalse :
      currentObservationAutomaticallyDeterminesContrast ≡ false

    contrastAutomaticallySufficientForEveryAction : Bool
    contrastAutomaticallySufficientForEveryActionIsFalse :
      contrastAutomaticallySufficientForEveryAction ≡ false

canonicalContrastiveHistoryBoundary : ContrastiveHistoryBoundary
canonicalContrastiveHistoryBoundary =
  contrastiveHistoryBoundary
    true refl
    true refl
    false refl
    false refl
