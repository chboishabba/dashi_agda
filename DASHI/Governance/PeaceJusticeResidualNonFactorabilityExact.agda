module DASHI.Governance.PeaceJusticeResidualNonFactorabilityExact where

------------------------------------------------------------------------
-- PEACE / JUSTICE RESIDUAL NON-FACTORABILITY
--
-- Reuses the existing quiet-surface countermodel and makes the structural
-- "no justice, no peace" reading precise without asserting that injustice
-- mechanically causes literal disorder.  An order-only observer cannot certify
-- justice closure when justice distinguishes fine states inside the same quiet
-- fibre.  Coercive disappearance of a visible disturbance is therefore not a
-- proof that the normative residual was resolved.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Governance.InstitutionPreservingRechartAntiSublationExact as Rechart

data JusticeResidualStatus : Set where
  residualResolved residualOpen : JusticeResidualStatus

justiceResidual : Rechart.OrderJusticeState → JusticeResidualStatus
justiceResidual Rechart.justQuietState = residualResolved
justiceResidual Rechart.suppressedQuietState = residualOpen
justiceResidual Rechart.visibleConflictState = residualOpen

quietStatesShareOrderSurface :
  Rechart.orderObserver Rechart.justQuietState
  ≡ Rechart.orderObserver Rechart.suppressedQuietState
quietStatesShareOrderSurface = refl

quietStatesDifferOnResidual :
  justiceResidual Rechart.justQuietState
  ≡ justiceResidual Rechart.suppressedQuietState → ⊥
quietStatesDifferOnResidual ()

record OrderOnlyPeaceCertificate : Set where
  constructor orderOnlyPeaceCertificate
  field
    observedState : Rechart.OrderJusticeState
    quietObserved :
      Rechart.orderObserver observedState ≡
      Rechart.orderObserver Rechart.justQuietState

open OrderOnlyPeaceCertificate public

suppressedQuietHasOrderOnlyPeaceCertificate : OrderOnlyPeaceCertificate
suppressedQuietHasOrderOnlyPeaceCertificate =
  orderOnlyPeaceCertificate Rechart.suppressedQuietState refl

record JusticeClosureCertificate (state : Rechart.OrderJusticeState) : Set where
  constructor justiceClosureCertificate
  field
    residualClosed : justiceResidual state ≡ residualResolved

open JusticeClosureCertificate public

orderOnlyPeaceDoesNotEstablishJusticeClosure :
  JusticeClosureCertificate Rechart.suppressedQuietState → ⊥
orderOnlyPeaceDoesNotEstablishJusticeClosure certificate with residualClosed certificate
... | ()

------------------------------------------------------------------------
-- A current chart can make "peace" require disappearance of the residual while
-- justice requires the residual remain expressible until genuinely resolved.
-- The conflict is in the chart's requirements, not proof that disorder follows.
------------------------------------------------------------------------

record CurrentChartPeaceJusticeConflict : Set where
  constructor currentChartPeaceJusticeConflict
  field
    currentState : Rechart.OrderJusticeState
    orderSurfaceQuiet :
      Rechart.orderObserver currentState
      ≡ Rechart.orderObserver Rechart.justQuietState
    unresolvedJusticeResidual :
      justiceResidual currentState ≡ residualOpen
    peaceCriterionRequiresResidualResolved :
      JusticeClosureCertificate currentState → ⊥

open CurrentChartPeaceJusticeConflict public

canonicalCurrentChartPeaceJusticeConflict : CurrentChartPeaceJusticeConflict
canonicalCurrentChartPeaceJusticeConflict =
  currentChartPeaceJusticeConflict
    Rechart.suppressedQuietState
    refl
    refl
    orderOnlyPeaceDoesNotEstablishJusticeClosure

-- The visible-conflict state and suppressed-quiet state retain the same open
-- justice residual even though their order surfaces differ.
visibleToSuppressedSurfaceChangePreservesResidual :
  justiceResidual Rechart.visibleConflictState
  ≡ justiceResidual Rechart.suppressedQuietState
visibleToSuppressedSurfaceChangePreservesResidual = refl

record CoerciveSurfaceClosureWithoutResidualClosure : Set where
  constructor coerciveSurfaceClosureWithoutResidualClosure
  field
    before after : Rechart.OrderJusticeState
    orderChanged :
      Rechart.orderObserver before ≡ Rechart.orderObserver after → ⊥
    residualUnchanged : justiceResidual before ≡ justiceResidual after

canonicalCoerciveSurfaceClosureWithoutResidualClosure :
  CoerciveSurfaceClosureWithoutResidualClosure
canonicalCoerciveSurfaceClosureWithoutResidualClosure =
  coerciveSurfaceClosureWithoutResidualClosure
    Rechart.visibleConflictState
    Rechart.suppressedQuietState
    (λ ())
    refl

record PeaceJusticeResidualBoundary : Set where
  constructor peaceJusticeResidualBoundary
  field
    quietOrderSurfaceCertifiesJustice : Bool
    coerciveSurfaceClosureCertifiesResidualClosure : Bool
    injusticeMechanicallyImpliesDisorder : Bool
    openJusticeResidualCanSurviveQuietSurface : Bool
    currentChartCanMakePeaceJusticeRequirementsConflict : Bool

canonicalPeaceJusticeResidualBoundary : PeaceJusticeResidualBoundary
canonicalPeaceJusticeResidualBoundary =
  peaceJusticeResidualBoundary false false false true true
