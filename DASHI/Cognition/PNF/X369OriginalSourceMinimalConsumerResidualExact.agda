module DASHI.Cognition.PNF.X369OriginalSourceMinimalConsumerResidualExact where

-- Reuse existing consumer-fibre repair, pairObserver and future-descent
-- owners. No new quotient ontology, no invented source semantics.
-- For ORIGINAL learned Bytes: a coarse chart may fail; a consumer-
-- relative retained residual repairs only the failures it separates.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Kernel checking deferred.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.FactorisationSpineCrosswalkExact as Factorisation
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

module OriginalConsumerResidual
  (Bytes Input Outcome Coarse Residual : Set)
  (actualLearnedStep : Input → Bytes → Bytes)
  (actualSourceReadout : Input → Bytes → Outcome)
  (originalCoarseGeometry : Bytes → Coarse)
  (retainedConsumerResidual : Bytes → Residual) where

  -- The existing owner for observer pairing is reused verbatim.
  repairedObserver : Bytes → Coarse × Residual
  repairedObserver =
    Observer.pairObserver originalCoarseGeometry retainedConsumerResidual

  -- All-source readout and successor squares are the only P0
  -- premises: they are not consequences of algebraic chart cardinality.
  module WithOriginalSourceSquares
    (sourceReadoutStable :
      (u : Input) (x y : Bytes) →
      repairedObserver x ≡ repairedObserver y →
      actualSourceReadout u x ≡ actualSourceReadout u y)
    (sourceSuccessorStable :
      (u : Input) (x y : Bytes) →
      repairedObserver x ≡ repairedObserver y →
      repairedObserver (actualLearnedStep u x) ≡
      repairedObserver (actualLearnedStep u y)) where

    originalEveryFiniteFuture :
      (word : List Input) (x y : Bytes) →
      repairedObserver x ≡ repairedObserver y →
      Future.trace actualLearnedStep actualSourceReadout word x ≡
      Future.trace actualLearnedStep actualSourceReadout word y
    originalEveryFiniteFuture =
      Future.inputIndexedTraceDescent
        actualLearnedStep actualSourceReadout repairedObserver
        sourceReadoutStable sourceSuccessorStable

    actualSourceConsumerSufficient :
      (u : Input) →
      Descent.ConsumerSufficient repairedObserver (actualSourceReadout u)
    actualSourceConsumerSufficient u =
      sourceReadoutStable u

    -- A source collision may only become visible after a DELAYED
    -- chronological original input word. Since the repaired observer
    -- preserves ALL finite futures by the original existing theorem,
    -- the already-owned fibre repair lemma forces a distinct retained
    -- residual for every such delayed original source separator.
    futureTraceSufficient :
      (word : List Input) →
      Descent.ConsumerSufficient repairedObserver
        (Future.trace actualLearnedStep actualSourceReadout word)
    futureTraceSufficient word x y same =
      originalEveryFiniteFuture word x y same

    originalDelayedCollisionMustRetainResidual :
      (word : List Input) →
      (w : Descent.ConsumerNonDescentWitness
          originalCoarseGeometry
          (Future.trace actualLearnedStep actualSourceReadout word)) →
      retainedConsumerResidual (Descent.left w) ≡
      retainedConsumerResidual (Descent.right w) → ⊥
    originalDelayedCollisionMustRetainResidual word witness =
      Repair.refinementRepairSeparatesWitness witness
        (futureTraceSufficient word)

    -- A witnessed collision of the COARSE source chart and a consumer
    -- necessarily lives in different retained residual fibres.
    -- Exactly the existing ConsumerFibreRepairExact theorem.
    originalCollisionMustRemainDistinguished :
      (u : Input) →
      (w : Descent.ConsumerNonDescentWitness
          originalCoarseGeometry (actualSourceReadout u)) →
      retainedConsumerResidual (Descent.left w) ≡
      retainedConsumerResidual (Descent.right w) → ⊥
    originalCollisionMustRemainDistinguished u w =
      Repair.refinementRepairSeparatesWitness w
        (actualSourceConsumerSufficient u)

  -- If a raw source-consumer collision is established before we can
  -- certify a repair, the canonical factorisation spine ALREADY rules
  -- out the proposed coarse quotient. It does NOT refute other more
  -- informative charts or exact whole-source residual retention.
  collisionRulesOutCoarseReadout :
    (u : Input) →
    Descent.ConsumerNonDescentWitness
      originalCoarseGeometry (actualSourceReadout u) →
    Descent.ConsumerSufficient
      originalCoarseGeometry (actualSourceReadout u) → ⊥
  collisionRulesOutCoarseReadout u witness =
    Descent.nonDescentWitnessBlocksSufficiency witness

  -- Runtime exact stable partitions are constructed separately by
  -- existing scripts/check_x369_nonlinear_closure.py refine and
  -- scripts/x369_future_realization.py on a truly successor-closed
  -- ORIGINAL source graph; finite minimality is not an Agda theorem
  -- about the full infinite float-history universe.
