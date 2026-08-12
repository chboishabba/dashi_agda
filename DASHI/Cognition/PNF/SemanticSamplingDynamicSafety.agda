module DASHI.Cognition.PNF.SemanticSamplingDynamicSafety where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Foundations.StratifiedResolutionTowerExact as Resolution
import DASHI.Cognition.PNF.SemanticSamplingLookupGeometry as Sampling
import DASHI.Cognition.PNF.TerminalisationDefectRegression as Regression

------------------------------------------------------------------------
-- A concrete two-level sampling tower for the residual counterexample.
--
-- At level 0 only the visible Boolean is retained.  Every positive level keeps
-- the full residual state.  The current Boolean query therefore commutes
-- exactly at the 1 -> 0 projection.
------------------------------------------------------------------------

residualSamplingCarrier : Nat → Set
residualSamplingCarrier zero = Bool
residualSamplingCarrier (suc n) = Regression.ResidualState

residualSamplingProject :
  ∀ {r} → residualSamplingCarrier (suc r) → residualSamplingCarrier r
residualSamplingProject {zero} = Regression.residualProjection
residualSamplingProject {suc r} = λ state → state

residualSamplingTower : Resolution.ResolutionTower
residualSamplingTower = record
  { Carrier = residualSamplingCarrier
  ; project = residualSamplingProject
  }

staticResidualQuerySufficiency :
  Sampling.QuerySufficiency residualSamplingTower zero Bool
staticResidualQuerySufficiency =
  Sampling.querySufficiency
    Regression.residualProjection
    (λ value → value)
    (λ fine → refl)

------------------------------------------------------------------------
-- Yet the same coarse projection is dynamically unsafe because the retained
-- residual can become visible after an admissible action.
------------------------------------------------------------------------

staticSufficiencyCoexistsWithTerminalisation :
  Dynamic.TerminalisationDefect
    Regression.residualSystem
    Regression.residualProjection
staticSufficiencyCoexistsWithTerminalisation =
  Regression.residualProjectionTerminalisationDefect

staticQuerySufficiencyDoesNotSupplyDynamicSafety :
  Dynamic.DynamicConsumerSafety
    Regression.residualSystem
    Regression.residualProjection →
  ⊥
staticQuerySufficiencyDoesNotSupplyDynamicSafety safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    staticSufficiencyCoexistsWithTerminalisation
