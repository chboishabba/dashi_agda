module DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardExact as Guard
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence

------------------------------------------------------------------------
-- Reachable Mabo target: a genuine inclusion-minimal rule cut is returned.
------------------------------------------------------------------------

maboGuardedCutSearch :
  Guard.searchReachableMinimalCut
    2 Regression.maboGraph Regression.maboFacts Regression.maboSurvival
  ≡ Search.found (Search.ruleKey Regression.maboSurvivalRule ∷ [])
maboGuardedCutSearch = refl

------------------------------------------------------------------------
-- Already-unreachable Pabai target: no vacuous empty cut is reported.
-- Repair/transformation search owns this lane instead.
------------------------------------------------------------------------

pabaiGuardedCutSearch :
  Guard.searchReachableMinimalCut
    1 Regression.pabaiGraph Regression.pabaiFacts Negligence.dutyProposition
  ≡ Search.notFound
pabaiGuardedCutSearch = refl

pabaiRepairSearchStillFindsCandidate :
  Search.firstReopeningTransformation 1 Negligence.dutyProposition
    (Regression.pabaiReformulationCandidate ∷ [])
  ≡ Search.found Regression.pabaiReformulationCandidate
pabaiRepairSearchStillFindsCandidate = refl
