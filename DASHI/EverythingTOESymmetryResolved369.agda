module DASHI.EverythingTOESymmetryResolved369 where

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Original investigative source-lineage and explicit non-promotion proofs.
-- Reuse the existing kernel-level claims. Do not infer physical events.
import DASHI.Wikimedia.IbrahimSnowballInvestigativeClaimSourceLineageBidiExact as SourceGenealogy
import DASHI.Cognition.HardtIbrahimSourceRootMaxCutExact as HardtCase
import DASHI.Cognition.HardtBrainInterventionNonidentifiabilityExact as NeuralCausality

-- Exact non-promotion results exposed at the TOE aggregate.
-- Their proofs belong to the imported canonical source and causal modules.
open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

toeCitationIsNotInspection :
  SourceGenealogy.CitationMeansInspected → ⊥
toeCitationIsNotInspection = SourceGenealogy.citationDoesNotMeanInspected

toePrimaryIsNotTruth :
  SourceGenealogy.PrimaryMeansTrue → ⊥
toePrimaryIsNotTruth = SourceGenealogy.primaryDoesNotMeanTrue

toeMentionsAreNotIndependentEvidence :
  SourceGenealogy.MentionCountMeansIndependentEvidence → ⊥
toeMentionsAreNotIndependentEvidence =
  SourceGenealogy.mentionCountDoesNotMeanIndependentEvidence

toeNoPassiveObservationDecoder :
  (decoder : Bool × Bool → Bool × Bool) →
  ((w : NeuralCausality.TrialWorld) →
    NeuralCausality.causalResponse w true ≡
    decoder (NeuralCausality.passiveObservation w)) → ⊥
toeNoPassiveObservationDecoder = NeuralCausality.noUniversalDoDecoder
