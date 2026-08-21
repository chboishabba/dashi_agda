module DASHI.Biology.Levin.CrossFrequencyEffectiveTopologyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.DynamicEffectiveTopology as Topology
import DASHI.Biology.Levin.MillerTravelingWaveAccessProducerExact as Miller

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- Mikael Lundqvist, Scott L. Brincat, Jonas Rose, Melissa R. Warden,
-- Timothy J. Buschman, Earl K. Miller, Pawel Herman,
-- "Working memory control dynamics follow principles of spatial computing"
-- (2023). DOI: 10.1038/s41467-023-36555-4.
--
-- The source motivates beta/gamma spatial control.  The exact finite gate below
-- is DASHI's theorem-level realization on the already-existing
-- DynamicEffectiveTopology carrier.
------------------------------------------------------------------------

data BetaControl : Set where
  betaHigh betaLow : BetaControl

data GammaContent : Set where
  gammaBurst : GammaContent

betaState : BetaControl → Topology.ElectrochemicalState
betaState betaHigh = Topology.inhibitedState
betaState betaLow = Topology.recurrentState

gammaReadable : BetaControl → GammaContent → Bool
gammaReadable betaHigh gammaBurst = false
gammaReadable betaLow gammaBurst = true

sameGammaDifferentBeta :
  gammaReadable betaHigh gammaBurst ≡ gammaReadable betaLow gammaBurst → ⊥
sameGammaDifferentBeta ()

betaLowOpensExistingAnatomicalEdge :
  Topology.EffectiveEdge
    (betaState betaLow)
    Topology.associationNode
    Topology.planningNode
betaLowOpensExistingAnatomicalEdge =
  Topology.recurrentAssociationPlanning

betaHighClosesSameAnatomicalEdge :
  Topology.EffectiveEdge
    (betaState betaHigh)
    Topology.associationNode
    Topology.planningNode → ⊥
betaHighClosesSameAnatomicalEdge =
  Topology.inhibitedAssociationPlanningImpossible

betaLowOpensTwoStepReach :
  Topology.Reachable
    (betaState betaLow)
    Topology.sensoryNode
    Topology.planningNode
betaLowOpensTwoStepReach =
  Topology.recurrentSensoryPlanningReach

------------------------------------------------------------------------
-- Traveling beta-like control can now feed the same effective-topology gate.
------------------------------------------------------------------------

travelingBetaAt : Miller.Tick2 → Miller.Site2 → BetaControl
travelingBetaAt Miller.firstTick Miller.leftSite = betaLow
travelingBetaAt Miller.firstTick Miller.rightSite = betaHigh
travelingBetaAt Miller.secondTick Miller.leftSite = betaHigh
travelingBetaAt Miller.secondTick Miller.rightSite = betaLow

travelingStencilFlipsLeftGate :
  travelingBetaAt Miller.firstTick Miller.leftSite
  ≡ travelingBetaAt Miller.secondTick Miller.leftSite → ⊥
travelingStencilFlipsLeftGate ()

record CrossFrequencyTopologyBoundary : Set where
  constructor crossFrequencyTopologyBoundary
  field
    betaLabelIsLiteralUniversalNeuralLaw : Bool
    gammaContentIsWholeSemanticState : Bool
    structuralEdgeEqualsFunctionalEdge : Bool
    oneFiniteGateProvesConsciousness : Bool

canonicalCrossFrequencyTopologyBoundary : CrossFrequencyTopologyBoundary
canonicalCrossFrequencyTopologyBoundary =
  crossFrequencyTopologyBoundary false false false false
