module DASHI.Physics.Chemistry.AtomicClosedShellSchurBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)

import DASHI.Analysis.FiniteOperatorReductionCore as FOR
import DASHI.Physics.Chemistry.AtomicShellRecurrence as ASR

------------------------------------------------------------------------
-- Feshbach/Schur reduction is the exact operator-theoretic join between the
-- existing NS/YM block analysis and the chemistry shell-recovery lane.
--
-- A chemistry implementation identifies a retained electronic subspace and an
-- eliminated complementary subspace.  The effective operator on the retained
-- subspace is a Schur complement.  A positive residual Schur gap can then be
-- transported into the chemistry-specific GapWitness and perturbation scale
-- required by ClosedShellProjectionLock.
--
-- This bridge does not manufacture that identification.  It proves that once
-- the identification and the two quantitative transports are supplied, the
-- existing Schur certificate really does close valence stability.
------------------------------------------------------------------------

record AtomicClosedShellSchurBridge
  {v s : Level}
  (S : ASR.AtomicShellRecurrence)
  (L : ASR.ClosedShellProjectionLock S)
  (Vector : Set v)
  (Scalar : Set s)
  (O : FOR.SchurOrderLaws Scalar)
  (Q : FOR.QuantitativeBlockSchur Vector Scalar O)
  : Set (lsuc (v ⊔ s)) where
  field
    state :
      ASR.AtomicShellRecurrence.AtomicState S

    perturbation :
      ASR.ClosedShellProjectionLock.Perturbation L

    closed :
      ASR.AtomicShellRecurrence.shellClosed S state

    residualGapToAtomicGap :
      FOR.StrictSchurGap O Q →
      ASR.ClosedShellProjectionLock.GapWitness L state

    residualGapControlsPerturbation :
      FOR.StrictSchurGap O Q →
      ASR.ClosedShellProjectionLock.SmallRelativeToGap L perturbation state

open AtomicClosedShellSchurBridge public

schurGapStabilizesValence :
  ∀ {v s}
    {S : ASR.AtomicShellRecurrence}
    {L : ASR.ClosedShellProjectionLock S}
    {Vector : Set v}
    {Scalar : Set s}
    {O : FOR.SchurOrderLaws Scalar}
    {Q : FOR.QuantitativeBlockSchur Vector Scalar O} →
  (B : AtomicClosedShellSchurBridge S L Vector Scalar O Q) →
  (gap : FOR.StrictSchurGap O Q) →
  ASR._≡_
    (ASR.AtomicShellRecurrence.valenceOf S
      (ASR.ClosedShellProjectionLock.PerturbedState L
        (perturbation B)
        (state B)))
    (ASR.AtomicShellRecurrence.valenceOf S (state B))
schurGapStabilizesValence {L = L} B gap =
  ASR.ClosedShellProjectionLock.valenceClassStable L
    (closed B)
    (residualGapToAtomicGap B gap)
    (residualGapControlsPerturbation B gap)

record AtomicClosedShellSchurCertificate
  {v s : Level}
  {S : ASR.AtomicShellRecurrence}
  {L : ASR.ClosedShellProjectionLock S}
  {Vector : Set v}
  {Scalar : Set s}
  {O : FOR.SchurOrderLaws Scalar}
  {Q : FOR.QuantitativeBlockSchur Vector Scalar O}
  (B : AtomicClosedShellSchurBridge S L Vector Scalar O Q)
  : Set (lsuc (v ⊔ s)) where
  field
    schurCertificate :
      FOR.QuantitativeSchurCertificate O Q

    valenceStable :
      ASR._≡_
        (ASR.AtomicShellRecurrence.valenceOf S
          (ASR.ClosedShellProjectionLock.PerturbedState L
            (perturbation B)
            (state B)))
        (ASR.AtomicShellRecurrence.valenceOf S (state B))

open AtomicClosedShellSchurCertificate public

certifyAtomicClosedShellFromSchur :
  ∀ {v s}
    {S : ASR.AtomicShellRecurrence}
    {L : ASR.ClosedShellProjectionLock S}
    {Vector : Set v}
    {Scalar : Set s}
    {O : FOR.SchurOrderLaws Scalar}
    {Q : FOR.QuantitativeBlockSchur Vector Scalar O} →
  (B : AtomicClosedShellSchurBridge S L Vector Scalar O Q) →
  (gap : FOR.StrictSchurGap O Q) →
  AtomicClosedShellSchurCertificate B
certifyAtomicClosedShellFromSchur {O = O} {Q = Q} B gap = record
  { schurCertificate = FOR.certifyQuantitativeSchur O Q gap
  ; valenceStable = schurGapStabilizesValence B gap
  }
