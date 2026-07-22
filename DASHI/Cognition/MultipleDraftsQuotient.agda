module DASHI.Cognition.MultipleDraftsQuotient where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)

import DASHI.Cognition.ResidualPhaseGeometry as RPG

------------------------------------------------------------------------
-- Two genuinely distinct hidden processing histories can have the same public
-- report and action consequence.  Their indistinguishability is relative to
-- that quotient; a finer observation functor may distinguish them.
------------------------------------------------------------------------

data DraftHistory : Set where
  orwellianHistory : DraftHistory
  stalinesqueHistory : DraftHistory

data PublicReport : Set where
  movingColourReport : PublicReport

data PublicAction : Set where
  reportButtonPressed : PublicAction

data DetailedTrace : Set where
  lateRevisionTrace : DetailedTrace
  earlyResolutionTrace : DetailedTrace

publicProjection : RPG.Projection DraftHistory PublicReport
publicProjection = record
  { observe = λ where
      orwellianHistory → movingColourReport
      stalinesqueHistory → movingColourReport
  }

actionProjection : RPG.Projection DraftHistory PublicAction
actionProjection = record
  { observe = λ where
      orwellianHistory → reportButtonPressed
      stalinesqueHistory → reportButtonPressed
  }

detailedProjection : RPG.Projection DraftHistory DetailedTrace
detailedProjection = record
  { observe = λ where
      orwellianHistory → lateRevisionTrace
      stalinesqueHistory → earlyResolutionTrace
  }

historiesAreDistinct :
  orwellianHistory ≡ stalinesqueHistory → ⊥
historiesAreDistinct ()

samePublicReport :
  RPG.Projection.observe publicProjection orwellianHistory
  ≡ RPG.Projection.observe publicProjection stalinesqueHistory
samePublicReport = refl

samePublicAction :
  RPG.Projection.observe actionProjection orwellianHistory
  ≡ RPG.Projection.observe actionProjection stalinesqueHistory
samePublicAction = refl

orwellianInPublicFibre : RPG.Fibre publicProjection movingColourReport
orwellianInPublicFibre = orwellianHistory , refl

stalinesqueInPublicFibre : RPG.Fibre publicProjection movingColourReport
stalinesqueInPublicFibre = stalinesqueHistory , refl

finerTraceDistinguishes :
  RPG.Projection.observe detailedProjection orwellianHistory
  ≡ lateRevisionTrace
finerTraceDistinguishes = refl

finerTraceAlsoDistinguishes :
  RPG.Projection.observe detailedProjection stalinesqueHistory
  ≡ earlyResolutionTrace
finerTraceAlsoDistinguishes = refl

------------------------------------------------------------------------
-- The exact DASHI conclusion: there is no distinction after the specified
-- public quotient, but no claim that the hidden histories are identical.
------------------------------------------------------------------------

record QuotientRelativeDraftResult : Set where
  constructor quotientRelativeDraftResult
  field
    hiddenHistoriesDistinct : orwellianHistory ≡ stalinesqueHistory → ⊥
    publicReportsEqual :
      RPG.Projection.observe publicProjection orwellianHistory
      ≡ RPG.Projection.observe publicProjection stalinesqueHistory
    publicActionsEqual :
      RPG.Projection.observe actionProjection orwellianHistory
      ≡ RPG.Projection.observe actionProjection stalinesqueHistory

canonicalDraftResult : QuotientRelativeDraftResult
canonicalDraftResult =
  quotientRelativeDraftResult
    historiesAreDistinct
    samePublicReport
    samePublicAction
