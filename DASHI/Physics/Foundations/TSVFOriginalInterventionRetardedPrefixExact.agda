{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalInterventionRetardedPrefixExact where

-- OBS01/OBS05 finite source producer, 2026-11-06.
-- Uses the ORIGINAL QuantumSurface.evolveKet and TSVFEnsemble fields.
-- A later intervention cannot rewrite an earlier, already produced
-- unconditioned observer record in this operational protocol.
-- This does NOT claim a continuum Kubo derivative, locality in space,
-- dimension four, an Einstein metric, or independence of an ABL
-- postselected conditional from a future measurement choice.
--
-- The two different statements are kept as different functions:
--   prefixRead: operational early record, before intervention;
--   terminalRead: later record, after the actual chosen intervention.
-- An operational causal front still needs physically located probes,
-- calibrated clock units, propagation bounds and continuum limits.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Quantum.TSVF as TSVF

module _
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  (EarlierRecord LaterRecord : Set)
  (readEarlier : TSVF.QuantumSurface.Ket Q → EarlierRecord)
  (readLater : TSVF.QuantumSurface.Ket Q → LaterRecord)
  where

  Ket = TSVF.QuantumSurface.Ket Q
  Operator = TSVF.QuantumSurface.Operator Q

  -- Exactly the original selected TSVF initial-to-middle ket, rather
  -- than a chosen surrogate state on a separately declared carrier.
  originalPrefixState : Ket
  originalPrefixState = TSVF.forwardState E

  -- An intervention is placed AFTER the earlier record was produced.
  originalPostPrefixState : Operator → Ket
  originalPostPrefixState intervention =
    TSVF.QuantumSurface.apply Q intervention originalPrefixState

  originalEarlierRecord : EarlierRecord
  originalEarlierRecord = readEarlier originalPrefixState

  originalTerminalRecord : Operator → LaterRecord
  originalTerminalRecord intervention =
    readLater
      (TSVF.QuantumSurface.evolveKet Q
        (TSVF.middleTime E)
        (TSVF.finalTime E)
        (originalPostPrefixState intervention))

  -- The earlier record genuinely uses original evolveKet, but it does
  -- not consume an intervention chosen after the prefix was recorded.
  originalEarlierRecordWithLaterChoice : Operator → EarlierRecord
  originalEarlierRecordWithLaterChoice intervention =
    readEarlier (TSVF.forwardState E)

  originalNoLaterChoiceRewritesEarlierRecord :
    (left right : Operator) →
    originalEarlierRecordWithLaterChoice left
      ≡ originalEarlierRecordWithLaterChoice right
  originalNoLaterChoiceRewritesEarlierRecord left right = refl

  originalPrefixReadIsSelectedTSVFRead :
    (intervention : Operator) →
    originalEarlierRecordWithLaterChoice intervention
      ≡ readEarlier
           (TSVF.QuantumSurface.evolveKet Q
             (TSVF.initialTime E)
             (TSVF.middleTime E)
             (TSVF.initialKet E))
  originalPrefixReadIsSelectedTSVFRead intervention = refl

  -- A downstream readout equality is obtained only when two actual
  -- evolved terminal kets agree; no generic no-response theorem.
  originalEqualTerminalKetsGiveEqualReadouts :
    (left right : Operator) →
    TSVF.QuantumSurface.evolveKet Q
      (TSVF.middleTime E) (TSVF.finalTime E)
      (originalPostPrefixState left)
      ≡
    TSVF.QuantumSurface.evolveKet Q
      (TSVF.middleTime E) (TSVF.finalTime E)
      (originalPostPrefixState right)
    →
    originalTerminalRecord left ≡ originalTerminalRecord right
  originalEqualTerminalKetsGiveEqualReadouts left right proof =
    cong readLater proof

  -- Given an actual later-intervention readout difference, the
  -- operational earlier result remains equal. This keeps retarded
  -- response different from post-selection/retro-conditioning.
  originalRetardedPairKeepsPrefix :
    (left right : Operator) →
    originalEarlierRecordWithLaterChoice left
      ≡ originalEarlierRecordWithLaterChoice right
  originalRetardedPairKeepsPrefix =
    originalNoLaterChoiceRewritesEarlierRecord
