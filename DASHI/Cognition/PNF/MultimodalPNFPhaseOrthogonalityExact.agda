module DASHI.Cognition.PNF.MultimodalPNFPhaseOrthogonalityExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OpticalTextCompressionPNFExact as Optical
import DASHI.Cognition.PNF.PhasedRelationalEvidencePropagationExact as Evidence
import DASHI.Cognition.PNF.PhasedRelationalLatticeExact as Lattice

------------------------------------------------------------------------
-- THREE ORTHOGONAL PHASE COORDINATES
--
-- 1. representation modality: text / visual / latent;
-- 2. process phase: the PNF/depth-wheel task grade;
-- 3. semantic phase: evidence-derived interaction direction.
--
-- The key point is not that all three are cyclic.  It is that they describe
-- different axes and therefore require different transition/equality laws.
------------------------------------------------------------------------

record MultimodalPNFCell : Set₁ where
  constructor multimodalPNFCell
  field
    modality : Optical.RepresentationModality
    cell :
      Lattice.PhasedLatticeCell
        {Subject = Evidence.Node}
        {CandidateType = Evidence.CandidateType}
        {Evidence = Evidence.Evidence}
        Evidence.eventNode Evidence.editionLike

open MultimodalPNFCell public

localTextCell : MultimodalPNFCell
localTextCell = multimodalPNFCell Optical.textModality Evidence.localCell

localVisualCell : MultimodalPNFCell
localVisualCell = multimodalPNFCell Optical.visualModality Evidence.localCell

expandedVisualCell : MultimodalPNFCell
expandedVisualCell = multimodalPNFCell Optical.visualModality Evidence.expandedCell

reencodeModality : Optical.RepresentationModality → MultimodalPNFCell → MultimodalPNFCell
reencodeModality target wrapped = multimodalPNFCell target (cell wrapped)

advanceProcess : MultimodalPNFCell → MultimodalPNFCell
advanceProcess wrapped =
  multimodalPNFCell
    (modality wrapped)
    (Lattice.advanceProcessPhase (cell wrapped))

------------------------------------------------------------------------
-- Modality phase is independent of process/semantic PNF state.
------------------------------------------------------------------------

modalityReencodingPreservesProcessPhase :
  (target : Optical.RepresentationModality) →
  (wrapped : MultimodalPNFCell) →
  Lattice.processPhase (cell (reencodeModality target wrapped))
  ≡ Lattice.processPhase (cell wrapped)
modalityReencodingPreservesProcessPhase target wrapped = refl

modalityReencodingPreservesSemanticPhase :
  (target : Optical.RepresentationModality) →
  (wrapped : MultimodalPNFCell) →
  Lattice.semanticPhase (cell (reencodeModality target wrapped))
  ≡ Lattice.semanticPhase (cell wrapped)
modalityReencodingPreservesSemanticPhase target wrapped = refl

modalityReencodingPreservesPressureEnvelope :
  (target : Optical.RepresentationModality) →
  (wrapped : MultimodalPNFCell) →
  Lattice.pressureEnvelope (cell (reencodeModality target wrapped))
  ≡ Lattice.pressureEnvelope (cell wrapped)
modalityReencodingPreservesPressureEnvelope target wrapped = refl

modalityReencodingCommutesWithProcessAdvance :
  (target : Optical.RepresentationModality) →
  (wrapped : MultimodalPNFCell) →
  reencodeModality target (advanceProcess wrapped)
  ≡ advanceProcess (reencodeModality target wrapped)
modalityReencodingCommutesWithProcessAdvance target wrapped = refl

------------------------------------------------------------------------
-- Evidence may change semantic phase while modality and process phase stay put.
------------------------------------------------------------------------

sameVisualModalityAcrossEvidenceUpdate :
  modality localVisualCell ≡ modality expandedVisualCell
sameVisualModalityAcrossEvidenceUpdate = refl

sameProcessPhaseAcrossEvidenceUpdate :
  Lattice.processPhase (cell localVisualCell)
  ≡ Lattice.processPhase (cell expandedVisualCell)
sameProcessPhaseAcrossEvidenceUpdate =
  Evidence.processPhaseUnchangedAcrossEvidenceExpansion

semanticPhaseChangesWithoutModalityChange :
  Lattice.semanticPhase (cell localVisualCell)
  ≡ Lattice.semanticPhase (cell expandedVisualCell) → ⊥
semanticPhaseChangesWithoutModalityChange = Evidence.semanticPhaseActuallyChanges

------------------------------------------------------------------------
-- Hence text->visual compression, process-phase advance, and semantic evidence
-- update are mathematically distinct transitions.  This is the PNF phase
-- discipline used by the multimodal/grokking bridge.
------------------------------------------------------------------------
