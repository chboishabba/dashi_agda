{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedTermReplayExact where

open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- Canonical residual owner for the historical CMP116/R409 selected-term lane.
--
-- PRIMARY SOURCE
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- SOURCE BOUNDARY / DASHI EXTENSION
-- The source motivates the selected localized differentiated-term structure.
-- This parameterized authority surface is a DASHI EXTENSION: it separates
-- transcription/replay receipts from the actual selected-term proof relation.
-- Neither receipt is theorem authority.
--
-- The historical `selectedTermIdentity` field is intentionally retired: the
-- selected term is now fixed as a parameter, so identity cannot be chosen by
-- the residual constructor.
--
-- The selected source, selected term, source-attachment predicate and proof
-- relation are fixed BEFORE the record is constructed.  The constructor can
-- therefore carry evidence for the selected equality, but cannot choose a
-- trivial carrier/relation in order to manufacture it.
------------------------------------------------------------------------

record CMP116CanonicalSelectedTermReplay
    (SelectedSource : Set)
    (selectedSource : SelectedSource)
    (SelectedTerm : Set)
    (selectedTerm : SelectedTerm)
    (SelectedTermBelongsToSource : SelectedSource → SelectedTerm → Set)
    (selectedTermSourceAttachment :
      SelectedTermBelongsToSource selectedSource selectedTerm)
    (ProofBearingEquality : SelectedSource → SelectedTerm → Set)
    (SourceTranscriptionReceipt ExecutionReplayReceipt : Set) : Set₁ where
  field
    sourceTranscriptionReceipt : SourceTranscriptionReceipt
    executionReplayReceipt : ExecutionReplayReceipt
    proofBearingEquality : ProofBearingEquality selectedSource selectedTerm

------------------------------------------------------------------------

open CMP116CanonicalSelectedTermReplay public

executionReplayCreatesProofEquality : Bool
executionReplayCreatesProofEquality = false

sourceTranscriptionCreatesProofEquality : Bool
sourceTranscriptionCreatesProofEquality = false

clayPromotion : Bool
clayPromotion = false
