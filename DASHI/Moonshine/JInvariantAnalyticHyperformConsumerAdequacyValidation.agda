module DASHI.Moonshine.JInvariantAnalyticHyperformConsumerAdequacyValidation where

open import Agda.Builtin.Bool using (Bool)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Foundations.HyperformChartGluingExact as Glue
import DASHI.Moonshine.JInvariantAnalyticHyperformChartGluingExact as Atlas
import DASHI.Moonshine.JInvariantAnalyticHyperformConsumerAdequacyExact as Adequacy

pantsPostprocessingCannotRepair :
  ∀ {M qE4 qE6 system Outcome}
    (atlas : Atlas.JInvariantAnalyticHyperformAtlas M qE4 qE6 system)
    (consumer : Atlas.Lattice.Parameter M → Outcome) →
  INF.NonFactorabilityWitness
    (Glue.observe (Atlas.parameterStructuredObserver atlas))
    consumer →
  INF.FactorsThrough
    (Glue.observe (Adequacy.parameterPantsObserver atlas))
    consumer →
  ⊥
pantsPostprocessingCannotRepair atlas consumer =
  Adequacy.pantsCannotRecoverStructuredObserverDistinction atlas
