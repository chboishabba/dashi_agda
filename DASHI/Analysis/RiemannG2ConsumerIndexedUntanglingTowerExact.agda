module DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Historical
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Refine

------------------------------------------------------------------------
-- RH / G2 INSTANTIATION OF THE CONSUMER-INDEXED UNTANGLING STEP
--
-- The existing direct finite-near attack already owns a concrete obstruction:
-- positivePhaseCell and negativePhaseCell have the same multiplicity and
-- absolute envelope but opposite signed phase contribution.  The final pole-near
-- refinement owner independently identifies target-relative phase as the first
-- missing observation coordinate.
--
-- This file packages that already-owned finite obstruction as one untangling
-- layer.  It does NOT manufacture the literal nearResponse representation,
-- target-translation/modulation theorem, strict joint margin, or RH.
------------------------------------------------------------------------

data RHCellWorld : Set where
  positivePhaseWorld : RHCellWorld
  negativePhaseWorld : RHCellWorld

materializeHistoricalCell : RHCellWorld → Historical.DirectFiniteNearCell
materializeHistoricalCell positivePhaseWorld = Historical.positivePhaseCell
materializeHistoricalCell negativePhaseWorld = Historical.negativePhaseCell

data CountEnvelopeCoarse : Set where
  sameUnitMultiplicityAndEnvelope : CountEnvelopeCoarse

data SignedPhaseResidual : Set where
  positiveSignedPhase : SignedPhaseResidual
  negativeSignedPhase : SignedPhaseResidual

coarseCountEnvelope : RHCellWorld → CountEnvelopeCoarse
coarseCountEnvelope _ = sameUnitMultiplicityAndEnvelope

signedPhaseResidual : RHCellWorld → SignedPhaseResidual
signedPhaseResidual positivePhaseWorld = positiveSignedPhase
signedPhaseResidual negativePhaseWorld = negativeSignedPhase

reopenRHCell : CountEnvelopeCoarse → SignedPhaseResidual → RHCellWorld
reopenRHCell sameUnitMultiplicityAndEnvelope positiveSignedPhase = positivePhaseWorld
reopenRHCell sameUnitMultiplicityAndEnvelope negativeSignedPhase = negativePhaseWorld

reopenRHCellExact :
  (world : RHCellWorld) →
  reopenRHCell (coarseCountEnvelope world) (signedPhaseResidual world) ≡ world
reopenRHCellExact positivePhaseWorld = refl
reopenRHCellExact negativePhaseWorld = refl

RHCellUntanglingGeometry : Set₁
RHCellUntanglingGeometry = Fibre.CoarseFineReopening RHCellWorld

rhCellUntanglingGeometry : RHCellUntanglingGeometry
rhCellUntanglingGeometry =
  Fibre.coarseFineReopening
    CountEnvelopeCoarse
    SignedPhaseResidual
    coarseCountEnvelope
    signedPhaseResidual
    reopenRHCell
    reopenRHCellExact

RHCellUntanglingTower : Set₁
RHCellUntanglingTower = Tower.UntanglingTower RHCellWorld 1

rhCellUntanglingTower : RHCellUntanglingTower
rhCellUntanglingTower = Tower.layer rhCellUntanglingGeometry Tower.terminal

rhCellTowerRoundTrip :
  (world : RHCellWorld) →
  Tower.decodeTower rhCellUntanglingTower
    (Tower.encodeTower rhCellUntanglingTower world)
  ≡ world
rhCellTowerRoundTrip = Tower.towerRoundTrip rhCellUntanglingTower

------------------------------------------------------------------------
-- The signed-phase-sensitive consumer witnesses failure of the coarse observer.
------------------------------------------------------------------------

data SignedResponseObservation : Set where
  positiveSignedResponse : SignedResponseObservation
  negativeSignedResponse : SignedResponseObservation

signedResponseObserve : RHCellWorld → SignedResponseObservation
signedResponseObserve positivePhaseWorld = positiveSignedResponse
signedResponseObserve negativePhaseWorld = negativeSignedResponse

RHCellFineSensitiveConsumer : Set
RHCellFineSensitiveConsumer =
  Fibre.FineSensitiveConsumer rhCellUntanglingGeometry signedResponseObserve

rhCellFineSensitiveConsumer : RHCellFineSensitiveConsumer
rhCellFineSensitiveConsumer =
  Fibre.fineSensitiveConsumer
    positivePhaseWorld
    negativePhaseWorld
    refl
    (λ ())
    "existing RH finite-near witness: equal multiplicity/absolute envelope, opposite signed phase response"

historicalCoarseCollisionWitness :
  Historical.sameCoarseObservation
    (materializeHistoricalCell positivePhaseWorld)
    (materializeHistoricalCell negativePhaseWorld)
historicalCoarseCollisionWitness = Historical.sameCountAndEnvelope

finalObserverRefinementBoundary : Refine.FinalPoleNearObserverRefinementBoundary
finalObserverRefinementBoundary = Refine.canonicalFinalPoleNearObserverRefinementBoundary

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record RHConsumerIndexedUntanglingBoundary : Set where
  constructor rh-consumer-indexed-untangling-boundary
  field
    genericUntanglingTowerReused : Bool
    historicalEqualCountEnvelopeCollisionReused : Bool
    countEnvelopeIsCoarseCoordinate : Bool
    signedPhaseIsRelativeFineCoordinate : Bool
    finiteWitnessReopensExactly : Bool
    coarseObserverFailsSignedResponseConsumer : Bool
    finalRHOwnerAlreadyNamesTargetRelativePhaseAsFirstMissingCoordinate : Bool
    finiteCellTowerPaysLiteralNearResponseRepresentation : Bool
    finiteCellTowerPaysTargetTranslationModulation : Bool
    finiteCellTowerPaysStrictJointMargin : Bool
    finiteCellTowerProvesRH : Bool
open RHConsumerIndexedUntanglingBoundary public

canonicalRHConsumerIndexedUntanglingBoundary :
  RHConsumerIndexedUntanglingBoundary
canonicalRHConsumerIndexedUntanglingBoundary =
  rh-consumer-indexed-untangling-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
