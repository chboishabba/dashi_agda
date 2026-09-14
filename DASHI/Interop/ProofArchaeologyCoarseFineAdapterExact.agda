module DASHI.Interop.ProofArchaeologyCoarseFineAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Interop.CrossLaneProofArchaeologyLedgerExact as Ledger

------------------------------------------------------------------------
-- PROOF ARCHAEOLOGY -> CANONICAL COARSE / RELATIVE-FINE REOPENING
--
-- A DatedAnchor contains both the compact surface used by current proof search
-- and chronology/provenance coordinates needed to interpret that surface.
-- We retain the latter as a relative-fine residual instead of flattening the
-- historical construction into the current theorem/payment view.
------------------------------------------------------------------------

record ProofAnchorSurface : Set where
  constructor proofAnchorSurfaceRecord
  field
    lane : Ledger.Lane
    owner : String
    object : String
    payment : Ledger.PaymentStatus

open ProofAnchorSurface public

record ProofAnchorResidual : Set where
  constructor proofAnchorResidualRecord
  field
    dateBrisbane : String
    commit : String
    clock : Ledger.HistoricalClock
    role : Ledger.HistoricalRole
    identity : Ledger.IdentityStatus
    interpretation : String

open ProofAnchorResidual public

proofAnchorSurface : Ledger.DatedAnchor → ProofAnchorSurface
proofAnchorSurface anchor =
  proofAnchorSurfaceRecord
    (Ledger.anchorLane anchor)
    (Ledger.owner anchor)
    (Ledger.object anchor)
    (Ledger.payment anchor)

proofAnchorResidual : Ledger.DatedAnchor → ProofAnchorResidual
proofAnchorResidual anchor =
  proofAnchorResidualRecord
    (Ledger.dateBrisbane anchor)
    (Ledger.commit anchor)
    (Ledger.clock anchor)
    (Ledger.role anchor)
    (Ledger.identity anchor)
    (Ledger.interpretation anchor)

reopenProofAnchor :
  ProofAnchorSurface → ProofAnchorResidual → Ledger.DatedAnchor
reopenProofAnchor surface residual =
  Ledger.dated-anchor
    (lane surface)
    (dateBrisbane residual)
    (commit residual)
    (owner surface)
    (object surface)
    (clock residual)
    (role residual)
    (identity residual)
    (payment surface)
    (interpretation residual)

proofAnchorReopenExact :
  (anchor : Ledger.DatedAnchor) →
  reopenProofAnchor
    (proofAnchorSurface anchor)
    (proofAnchorResidual anchor)
  ≡ anchor
proofAnchorReopenExact
  (Ledger.dated-anchor lane₀ date₀ commit₀ owner₀ object₀ clock₀ role₀ identity₀ payment₀ interpretation₀) = refl

proofAnchorReopening :
  Fibre.CoarseFineReopening Ledger.DatedAnchor
proofAnchorReopening =
  Fibre.coarseFineReopening
    ProofAnchorSurface
    ProofAnchorResidual
    proofAnchorSurface
    proofAnchorResidual
    reopenProofAnchor
    proofAnchorReopenExact

proofAnchorObserver =
  Fibre.coarseFineObserver proofAnchorReopening

proofAnchorObserverSeparating :
  (left right : Ledger.DatedAnchor) →
  proofAnchorObserver left ≡ proofAnchorObserver right →
  left ≡ right
proofAnchorObserverSeparating =
  Fibre.coarseFineObserverSeparating proofAnchorReopening

surfacePlusResidualDeterminesAnchor :
  {left right : Ledger.DatedAnchor} →
  proofAnchorSurface left ≡ proofAnchorSurface right →
  proofAnchorResidual left ≡ proofAnchorResidual right →
  left ≡ right
surfacePlusResidualDeterminesAnchor =
  Fibre.coarseAndRelativeFineDetermineState proofAnchorReopening

------------------------------------------------------------------------
-- Any concrete chronology/provenance-sensitive consumer of anchors can now use
-- the repo-wide projection-collision theorem directly.  No collision pair is
-- fabricated here; callers must provide the existing FineSensitiveConsumer.
------------------------------------------------------------------------

proofResidualSensitiveConsumerProjectsToCollision :
  ∀ {Observation : Set}
    {observe : Ledger.DatedAnchor → Observation} →
  Fibre.FineSensitiveConsumer proofAnchorReopening observe →
  Calculus.ProjectionCollision proofAnchorSurface observe
proofResidualSensitiveConsumerProjectsToCollision witness =
  Calculus.projectionCollision
    (Fibre.left witness)
    (Fibre.right witness)
    (Fibre.sameCoarse witness)
    (Fibre.consumerSeparates witness)

proofResidualSensitiveConsumerRefutesSurfaceOnly :
  ∀ {Observation : Set}
    {observe : Ledger.DatedAnchor → Observation} →
  Fibre.FineSensitiveConsumer proofAnchorReopening observe →
  (surfaceObserve : ProofAnchorSurface → Observation) →
  ((anchor : Ledger.DatedAnchor) →
    observe anchor ≡ surfaceObserve (proofAnchorSurface anchor)) →
  ⊥
proofResidualSensitiveConsumerRefutesSurfaceOnly witness =
  Calculus.consumerCannotFactorThroughProjection
    (proofResidualSensitiveConsumerProjectsToCollision witness)

record ProofArchaeologyCoarseFineBoundary : Set where
  constructor proofArchaeologyCoarseFineBoundary
  field
    currentSurfaceRetainsLaneOwnerObjectPayment : Bool
    residualRetainsChronologyCommitRoleIdentityInterpretation : Bool
    exactReopeningAvailable : Bool
    currentSurfaceIsWholeProofHistory : Bool
    chronologyResidualCanBeDroppedWithoutInformationLoss : Bool
    currentPaymentStatusRewritesHistoricalStatus : Bool

canonicalProofArchaeologyCoarseFineBoundary : ProofArchaeologyCoarseFineBoundary
canonicalProofArchaeologyCoarseFineBoundary =
  proofArchaeologyCoarseFineBoundary
    true
    true
    true
    false
    false
    false
