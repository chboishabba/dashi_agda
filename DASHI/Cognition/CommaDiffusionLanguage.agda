module DASHI.Cognition.CommaDiffusionLanguage where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.CognitiveResearchSources as Sources

------------------------------------------------------------------------
-- Research contact.
--
-- Discrete diffusion basis:
--   Austin, Johnson, Ho, Tarlow & van den Berg (NeurIPS 2021),
--   arXiv:2107.03006.
--   Li, Thickstun, Gulrajani, Liang & Hashimoto (NeurIPS 2022),
--   arXiv:2205.14217.
--   Sahoo et al. (NeurIPS 2024), arXiv:2406.07524.
--   Shi, Han, Wang, Doucet & Titsias (NeurIPS 2024), arXiv:2406.04329.
--
-- These papers motivate iterative whole-sequence refinement.  They do not
-- state the comma fixed-point theorem below; that is the DASHI construction.
------------------------------------------------------------------------

diffusionSources : List Sources.ResearchSource
diffusionSources =
  Sources.austinDiscreteDiffusion ∷
  Sources.liDiffusionLM ∷
  Sources.sahooMaskedDiffusionLM ∷
  Sources.shiGeneralizedMaskedDiffusion ∷ []

------------------------------------------------------------------------
-- Finite sentence carrier.
------------------------------------------------------------------------

data Clause : Set where
  blankClause
  feltSelfClause
  desiredSelfClause
  compelledSelfClause
  reconciledSelfClause : Clause

data Boundary : Set where
  commaBoundary
  periodBoundary : Boundary

data RelationKind : Set where
  coordination
  contrast
  apposition
  qualification
  repair : RelationKind

record DiffusionSentence : Set where
  constructor sentence
  field
    leftClause  : Clause
    boundary    : Boundary
    rightClause : Clause
    relation    : RelationKind

open DiffusionSentence public

------------------------------------------------------------------------
-- Joint denoising.  Each side can depend on the other; the punctuation anchor
-- and the relation coordinate are preserved.
------------------------------------------------------------------------

refineLeft : Clause → Clause → Clause
refineLeft blankClause desiredSelfClause = feltSelfClause
refineLeft blankClause compelledSelfClause = feltSelfClause
refineLeft left right = left

refineRight : Clause → Clause → Clause
refineRight feltSelfClause blankClause = desiredSelfClause
refineRight compelledSelfClause blankClause = compelledSelfClause
refineRight desiredSelfClause blankClause = reconciledSelfClause
refineRight left right = right

denoiseSentence : DiffusionSentence → DiffusionSentence
denoiseSentence (sentence left anchor right relationKind) =
  sentence
    (refineLeft left right)
    anchor
    (refineRight left right)
    relationKind

commaProjection : DiffusionSentence → Boundary
commaProjection = boundary

relationProjection : DiffusionSentence → RelationKind
relationProjection = relation

commaIsDiffusionFixedPoint :
  (left right : Clause) → (relationKind : RelationKind) →
  commaProjection
    (denoiseSentence
      (sentence left commaBoundary right relationKind))
  ≡ commaBoundary
commaIsDiffusionFixedPoint left right relationKind = refl

commaRelationIsInvariant :
  (left right : Clause) → (relationKind : RelationKind) →
  relationProjection
    (denoiseSentence
      (sentence left commaBoundary right relationKind))
  ≡ relationKind
commaRelationIsInvariant left right relationKind = refl

rightRefinementDependsOnLeft :
  refineRight feltSelfClause blankClause ≡ desiredSelfClause
rightRefinementDependsOnLeft = refl

changedLeftChangesRightRefinement :
  refineRight compelledSelfClause blankClause ≡ compelledSelfClause
changedLeftChangesRightRefinement = refl

leftCanBeRecoveredAtInterruption : DiffusionSentence → Clause
leftCanBeRecoveredAtInterruption = leftClause

interruptedExample : DiffusionSentence
interruptedExample =
  sentence feltSelfClause commaBoundary blankClause contrast

interruptionRecoversCoarseBasis :
  leftCanBeRecoveredAtInterruption interruptedExample ≡ feltSelfClause
interruptionRecoversCoarseBasis = refl

------------------------------------------------------------------------
-- PDA-style comma frame: hold the completed/coarse left constituent, leave a
-- relation obligation open, then reconcile after right-side refinement.
------------------------------------------------------------------------

record CommaFrame : Set where
  constructor commaFrame
  field
    heldLeft       : Clause
    openRelation   : RelationKind
    pendingRight   : Clause

open CommaFrame public

pushCommaFrame : Clause → RelationKind → CommaFrame
pushCommaFrame left relationKind =
  commaFrame left relationKind blankClause

refineCommaFrame : CommaFrame → CommaFrame
refineCommaFrame (commaFrame left relationKind right) =
  commaFrame left relationKind (refineRight left right)

reconcileFrame : CommaFrame → Clause
reconcileFrame (commaFrame feltSelfClause contrast desiredSelfClause) =
  reconciledSelfClause
reconcileFrame frame = heldLeft frame

heldLeftSurvivesRefinement :
  (left : Clause) → (relationKind : RelationKind) →
  heldLeft (refineCommaFrame (pushCommaFrame left relationKind)) ≡ left
heldLeftSurvivesRefinement left relationKind = refl

canonicalSelfCommaReconciles :
  reconcileFrame
    (refineCommaFrame
      (pushCommaFrame feltSelfClause contrast))
  ≡ reconciledSelfClause
canonicalSelfCommaReconciles = refl

------------------------------------------------------------------------
-- Ternary diffusion grammar.
--
-- neg  : candidate ruled out
-- zero : candidate remains admissible but unbound
-- pos  : provisional or final selection
--
-- Early refinement may return pos to zero; cooling/finalisation later maps
-- zero to a binding decision.
------------------------------------------------------------------------

revisePrematureCommitment : BT.Trit → BT.Trit
revisePrematureCommitment BT.pos = BT.zero
revisePrematureCommitment value = value

finaliseCandidate : BT.Trit → BT.Trit
finaliseCandidate BT.zero = BT.pos
finaliseCandidate value = value

prematurePositiveCanReturnToZero :
  revisePrematureCommitment BT.pos ≡ BT.zero
prematurePositiveCanReturnToZero = refl

projectiveCandidateCanFinalise :
  finaliseCandidate BT.zero ≡ BT.pos
projectiveCandidateCanFinalise = refl

------------------------------------------------------------------------
-- Concrete MDL reading: one cheap relation anchor can beat an unstructured
-- joint encoding.  Costs are finite code lengths, not empirical language-model
-- estimates.
------------------------------------------------------------------------

structuredCommaCost : Nat
structuredCommaCost = 3 + 3 + 1

unstructuredJointCost : Nat
unstructuredJointCost = 9

commaCompressionWitness : structuredCommaCost ≤ unstructuredJointCost
commaCompressionWitness =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
