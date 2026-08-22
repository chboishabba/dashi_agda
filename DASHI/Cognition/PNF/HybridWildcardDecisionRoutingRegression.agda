{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.HybridWildcardDecisionRoutingRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.HybridWildcardDecisionRoutingExact

------------------------------------------------------------------------
-- Finite dispatcher regression.
--
-- One demand has a certified bounded observation equal to the legacy resolution
-- observation.  A second demand has unresolved ambiguity and therefore carries
-- a residual through the legacy fallback.  The whole dispatcher is exact even
-- though only one demand is optimized.
------------------------------------------------------------------------

data Demand : Set where
  certifiedDemand residualDemand : Demand

data Observation : Set where
  candidateSetA candidateSetB : Observation

data Residual : Set where
  unresolvedScoreAndProducerFibre : Residual

certifiedDecision : HybridDecision Observation Residual
certifiedDecision =
  boundedCertified candidateSetA candidateSetA refl

residualDecision : HybridDecision Observation Residual
residualDecision =
  residualFallback candidateSetB unresolvedScoreAndProducerFibre

finiteDispatcher : ProofDirectedHybridDispatcher Demand Observation Residual
finiteDispatcher = record
  { decide = choose
  }
  where
    choose : Demand → HybridDecision Observation Residual
    choose certifiedDemand = certifiedDecision
    choose residualDemand = residualDecision

certifiedDemandUsesBoundedRoute :
  routeOf (decide finiteDispatcher certifiedDemand) ≡ certifiedBoundedRoute
certifiedDemandUsesBoundedRoute = refl

residualDemandUsesLegacyRoute :
  routeOf (decide finiteDispatcher residualDemand) ≡ residualLegacyRoute
residualDemandUsesLegacyRoute = refl

certifiedDemandObservationExact :
  chosenObservation (decide finiteDispatcher certifiedDemand)
    ≡ legacyObservationOf (decide finiteDispatcher certifiedDemand)
certifiedDemandObservationExact =
  hybridDispatcherIsExtensionallyExact finiteDispatcher certifiedDemand

residualDemandObservationExact :
  chosenObservation (decide finiteDispatcher residualDemand)
    ≡ legacyObservationOf (decide finiteDispatcher residualDemand)
residualDemandObservationExact =
  hybridDispatcherIsExtensionallyExact finiteDispatcher residualDemand

------------------------------------------------------------------------
-- Routing sufficiency is deliberately weaker than fine reconstruction.
--
-- Both decisions have exact declared consumer observations, but nothing in the
-- dispatcher supplies a theorem that residual score/provenance coordinates have
-- been reconstructed on the certified branch.  This empty permission blocks
-- accidental promotion of route safety into fine-state identity.
------------------------------------------------------------------------

data RoutingSafetyImpliesFineReconstructionPermission : Set where

routingSafetyDoesNotImplyFineReconstruction :
  RoutingSafetyImpliesFineReconstructionPermission → ⊥
routingSafetyDoesNotImplyFineReconstruction ()

------------------------------------------------------------------------
-- Residual fallback is not failure.  The unresolved fibre still has a route and
-- remains represented; only the fast execution policy is withheld.
------------------------------------------------------------------------

data ResidualWasRefutedPermission : Set where

fallbackDoesNotRefuteResidual : ResidualWasRefutedPermission → ⊥
fallbackDoesNotRefuteResidual ()
