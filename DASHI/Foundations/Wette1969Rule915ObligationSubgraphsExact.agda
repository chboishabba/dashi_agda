module DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: TWO L-OBLIGATION SUBGRAPHS WITH SHARED CORE
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
--
-- Section 1.632 states the dependency geometry explicitly:
--   * premises 8--15 belong to premise 18; 16--17 abbreviate premise 18;
--   * premises 19--25 together with 10--15 belong to premise 27;
--     premise 26 abbreviates premise 27.
--
-- Therefore premises 10--15 are a genuine shared subgraph, not duplicated
-- requirements.  This module factors the still-transcription-indexed L block
-- into one shared core plus the induction and independence branches.  It does
-- not guess OCR-sensitive formula bodies; it makes their proof dependency
-- reusable and exact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

Formula = Signature.Formula
Context = Finite.DerivationContext

slotFormula : Rule915.Rule915PremiseTranscription → Critical.Premise915 → Formula
slotFormula transcription = Rule915.premiseAt transcription

record FirstSevenEvidence
    (context : Context)
    (transcription : Rule915.Rule915PremiseTranscription) : Set where
  constructor firstSevenEvidence
  field
    e01 : slotFormula transcription Critical.p01 Finite.∈Context context
    e02 : slotFormula transcription Critical.p02 Finite.∈Context context
    e03 : slotFormula transcription Critical.p03 Finite.∈Context context
    e04 : slotFormula transcription Critical.p04 Finite.∈Context context
    e05 : slotFormula transcription Critical.p05 Finite.∈Context context
    e06 : slotFormula transcription Critical.p06 Finite.∈Context context
    e07 : slotFormula transcription Critical.p07 Finite.∈Context context

open FirstSevenEvidence public

record Shared1015Evidence
    (context : Context)
    (transcription : Rule915.Rule915PremiseTranscription) : Set where
  constructor shared1015Evidence
  field
    e10 : slotFormula transcription Critical.p10 Finite.∈Context context
    e11 : slotFormula transcription Critical.p11 Finite.∈Context context
    e12 : slotFormula transcription Critical.p12 Finite.∈Context context
    e13 : slotFormula transcription Critical.p13 Finite.∈Context context
    e14 : slotFormula transcription Critical.p14 Finite.∈Context context
    e15 : slotFormula transcription Critical.p15 Finite.∈Context context

open Shared1015Evidence public

record PredecessorInductionBranch
    (context : Context)
    (transcription : Rule915.Rule915PremiseTranscription)
    (shared : Shared1015Evidence context transcription) : Set where
  constructor predecessorInductionBranch
  field
    e08 : slotFormula transcription Critical.p08 Finite.∈Context context
    e09 : slotFormula transcription Critical.p09 Finite.∈Context context
    e16 : slotFormula transcription Critical.p16 Finite.∈Context context
    e17 : slotFormula transcription Critical.p17 Finite.∈Context context
    e18 : slotFormula transcription Critical.p18 Finite.∈Context context

open PredecessorInductionBranch public

record DefiniensIndependenceBranch
    (context : Context)
    (transcription : Rule915.Rule915PremiseTranscription)
    (shared : Shared1015Evidence context transcription) : Set where
  constructor definiensIndependenceBranch
  field
    e19 : slotFormula transcription Critical.p19 Finite.∈Context context
    e20 : slotFormula transcription Critical.p20 Finite.∈Context context
    e21 : slotFormula transcription Critical.p21 Finite.∈Context context
    e22 : slotFormula transcription Critical.p22 Finite.∈Context context
    e23 : slotFormula transcription Critical.p23 Finite.∈Context context
    e24 : slotFormula transcription Critical.p24 Finite.∈Context context
    e25 : slotFormula transcription Critical.p25 Finite.∈Context context
    e26 : slotFormula transcription Critical.p26 Finite.∈Context context
    e27 : slotFormula transcription Critical.p27 Finite.∈Context context

open DefiniensIndependenceBranch public

record Rule915ObligationEvidence
    (context : Context)
    (transcription : Rule915.Rule915PremiseTranscription) : Set where
  constructor rule915ObligationEvidence
  field
    formation : FirstSevenEvidence context transcription
    shared1015 : Shared1015Evidence context transcription
    inductionBranch :
      PredecessorInductionBranch context transcription shared1015
    independenceBranch :
      DefiniensIndependenceBranch context transcription shared1015

open Rule915ObligationEvidence public

-- One slot-indexed eliminator makes the non-duplication visible: slots 10--15
-- are read only from `shared1015`, and both major branches point to that same
-- proof object.
slotEvidence :
  {context : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  Rule915ObligationEvidence context transcription →
  (slot : Critical.Premise915) →
  slotFormula transcription slot Finite.∈Context context
slotEvidence evidence Critical.p01 = e01 (formation evidence)
slotEvidence evidence Critical.p02 = e02 (formation evidence)
slotEvidence evidence Critical.p03 = e03 (formation evidence)
slotEvidence evidence Critical.p04 = e04 (formation evidence)
slotEvidence evidence Critical.p05 = e05 (formation evidence)
slotEvidence evidence Critical.p06 = e06 (formation evidence)
slotEvidence evidence Critical.p07 = e07 (formation evidence)
slotEvidence evidence Critical.p08 = e08 (inductionBranch evidence)
slotEvidence evidence Critical.p09 = e09 (inductionBranch evidence)
slotEvidence evidence Critical.p10 = e10 (shared1015 evidence)
slotEvidence evidence Critical.p11 = e11 (shared1015 evidence)
slotEvidence evidence Critical.p12 = e12 (shared1015 evidence)
slotEvidence evidence Critical.p13 = e13 (shared1015 evidence)
slotEvidence evidence Critical.p14 = e14 (shared1015 evidence)
slotEvidence evidence Critical.p15 = e15 (shared1015 evidence)
slotEvidence evidence Critical.p16 = e16 (inductionBranch evidence)
slotEvidence evidence Critical.p17 = e17 (inductionBranch evidence)
slotEvidence evidence Critical.p18 = e18 (inductionBranch evidence)
slotEvidence evidence Critical.p19 = e19 (independenceBranch evidence)
slotEvidence evidence Critical.p20 = e20 (independenceBranch evidence)
slotEvidence evidence Critical.p21 = e21 (independenceBranch evidence)
slotEvidence evidence Critical.p22 = e22 (independenceBranch evidence)
slotEvidence evidence Critical.p23 = e23 (independenceBranch evidence)
slotEvidence evidence Critical.p24 = e24 (independenceBranch evidence)
slotEvidence evidence Critical.p25 = e25 (independenceBranch evidence)
slotEvidence evidence Critical.p26 = e26 (independenceBranch evidence)
slotEvidence evidence Critical.p27 = e27 (independenceBranch evidence)

premise10SharedByBothObligations :
  {context : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (evidence : Rule915ObligationEvidence context transcription) →
  slotFormula transcription Critical.p10 Finite.∈Context context
premise10SharedByBothObligations evidence = e10 (shared1015 evidence)

record Wette1969Rule915ObligationSubgraphsBoundary : Set where
  constructor wette1969Rule915ObligationSubgraphsBoundary
  field
    premises10To15OwnedByOneSharedEvidenceObject : Bool
    premises10To15OwnedByOneSharedEvidenceObjectIsTrue :
      premises10To15OwnedByOneSharedEvidenceObject ≡ true
    inductionAndIndependenceBranchesRemainDistinct : Bool
    inductionAndIndependenceBranchesRemainDistinctIsTrue :
      inductionAndIndependenceBranchesRemainDistinct ≡ true
    sourceDependencyGraphNowControlsProofPackaging : Bool
    sourceDependencyGraphNowControlsProofPackagingIsTrue :
      sourceDependencyGraphNowControlsProofPackaging ≡ true
    proofPackagingAlreadyRecoversAllLiteralLPremiseBodies : Bool
    proofPackagingAlreadyRecoversAllLiteralLPremiseBodiesIsFalse :
      proofPackagingAlreadyRecoversAllLiteralLPremiseBodies ≡ false

canonicalWette1969Rule915ObligationSubgraphsBoundary :
  Wette1969Rule915ObligationSubgraphsBoundary
canonicalWette1969Rule915ObligationSubgraphsBoundary =
  wette1969Rule915ObligationSubgraphsBoundary
    true refl true refl true refl false refl
