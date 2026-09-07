module DASHI.Core.ProjectionHierarchyCompatibleFibreBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact as Query

------------------------------------------------------------------------
-- PROJECTION HIERARCHY -> PARTIAL IDENTIFICATION FIBRES
--
-- Reverse x-pollination from Lean Instances.ProjectionHierarchy plus
-- PartialIdentification.  Instead of assigning a numeric percent identified,
-- each stronger observation owns an explicitly smaller compatible fibre.
------------------------------------------------------------------------

record StrictFibreRefinement {Hidden : Set}
    (stronger weaker : Bidi.ResidualFibre Hidden) : Set₁ where
  constructor strict-fibre-refinement
  field
    refines : Bidi.FibreRefines stronger weaker
    witness : Σ Hidden (λ hidden → weaker hidden × ¬ (stronger hidden))

open StrictFibreRefinement public

data Hidden : Set where h0 h1 h2 h3 : Hidden

coarseFibre : Bidi.ResidualFibre Hidden
coarseFibre h0 = ⊤
coarseFibre h1 = ⊤
coarseFibre h2 = ⊤
coarseFibre h3 = ⊤

middleFibre : Bidi.ResidualFibre Hidden
middleFibre h0 = ⊤
middleFibre h1 = ⊤
middleFibre h2 = ⊥
middleFibre h3 = ⊥

fineFibre : Bidi.ResidualFibre Hidden
fineFibre h0 = ⊤
fineFibre h1 = ⊥
fineFibre h2 = ⊥
fineFibre h3 = ⊥

middleRefinesCoarse : Bidi.FibreRefines middleFibre coarseFibre
middleRefinesCoarse h0 live = tt
middleRefinesCoarse h1 live = tt
middleRefinesCoarse h2 ()
middleRefinesCoarse h3 ()

fineRefinesMiddle : Bidi.FibreRefines fineFibre middleFibre
fineRefinesMiddle h0 live = tt
fineRefinesMiddle h1 ()
fineRefinesMiddle h2 ()
fineRefinesMiddle h3 ()

middleStrictlyRefinesCoarse : StrictFibreRefinement middleFibre coarseFibre
middleStrictlyRefinesCoarse =
  strict-fibre-refinement middleRefinesCoarse (h2 , (tt , (λ x → x)))

fineStrictlyRefinesMiddle : StrictFibreRefinement fineFibre middleFibre
fineStrictlyRefinesMiddle =
  strict-fibre-refinement fineRefinesMiddle (h1 , (tt , (λ x → x)))

data Decision : Set where accepted rejected : Decision

middleDecision : Hidden → Decision
middleDecision h0 = accepted
middleDecision h1 = accepted
middleDecision h2 = rejected
middleDecision h3 = rejected

middleConsumerClosed : Bidi.PointIdentifies middleFibre middleDecision
middleConsumerClosed h0 h0 left right = refl
middleConsumerClosed h0 h1 left right = refl
middleConsumerClosed h0 h2 left ()
middleConsumerClosed h0 h3 left ()
middleConsumerClosed h1 h0 left right = refl
middleConsumerClosed h1 h1 left right = refl
middleConsumerClosed h1 h2 left ()
middleConsumerClosed h1 h3 left ()
middleConsumerClosed h2 right ()
middleConsumerClosed h3 right ()

h0NotH1 : h0 ≡ h1 → ⊥
h0NotH1 ()

middleNotPointSingleton :
  (∀ left right → middleFibre left → middleFibre right → left ≡ right) → ⊥
middleNotPointSingleton point = h0NotH1 (point h0 h1 tt tt)

record ProjectionHierarchyBoundary : Set where
  constructor projection-hierarchy-boundary
  field
    strongerProjectionMayStrictlyShrinkFibre : Bool
    consumerMayCloseBeforeSingleton : Bool
    numericIdentificationFractionRequired : Bool
    strictHierarchyAutomaticallyIdentifiesMechanism : Bool

canonicalProjectionHierarchyBoundary : ProjectionHierarchyBoundary
canonicalProjectionHierarchyBoundary =
  projection-hierarchy-boundary true true false false
