module DASHI.Core.EpistemicSuspensionExact where

------------------------------------------------------------------------
-- GENERIC EPISTEMIC SUSPENSION / REFINE-BEFORE-COLLAPSE
--
-- Source basis:
--   User-supplied DASHI origin/reconstruction notes explicitly recover the
--   operational ternary rule:
--
--     -1 -> reject here
--      0 -> go deeper in tree
--     +1 -> accept here
--
--   and distinguish this from the later operational motif enum.  Current
--   DialecticMotifKernel maps several concrete states to M5/buffer, but the
--   reusable epistemic concept should not depend on that legacy motif label.
--
-- Repo cross-pollination:
--   LevelIndexedProofObligationHyperformalismExact already owns the richer
--   rechart-before-decision case when evidence is present but applicability is
--   outside the current comparison scope.  This module owns only the generic
--   three-way disposition and its no-collapse boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Generic epistemic disposition.
------------------------------------------------------------------------

data EpistemicDisposition : Set where
  rejectHere suspendAndRefine acceptHere : EpistemicDisposition

data TernaryEvidence : Set where
  negativeEvidence neutralEvidence positiveEvidence : TernaryEvidence

disposition : TernaryEvidence → EpistemicDisposition
disposition negativeEvidence = rejectHere
disposition neutralEvidence = suspendAndRefine
disposition positiveEvidence = acceptHere

neutralMeansSuspendAndRefine :
  disposition neutralEvidence ≡ suspendAndRefine
neutralMeansSuspendAndRefine = refl

negativeIsNotNeutral :
  disposition negativeEvidence ≡ disposition neutralEvidence → ⊥
negativeIsNotNeutral ()

positiveIsNotNeutral :
  disposition positiveEvidence ≡ disposition neutralEvidence → ⊥
positiveIsNotNeutral ()

------------------------------------------------------------------------
-- A binary collapse cannot faithfully identify suspension with rejection or
-- acceptance without losing the three-way decision surface.
------------------------------------------------------------------------

data BinaryDecision : Set where
  no yes : BinaryDecision

collapseNeutralToNo : TernaryEvidence → BinaryDecision
collapseNeutralToNo negativeEvidence = no
collapseNeutralToNo neutralEvidence = no
collapseNeutralToNo positiveEvidence = yes

collapseNeutralToYes : TernaryEvidence → BinaryDecision
collapseNeutralToYes negativeEvidence = no
collapseNeutralToYes neutralEvidence = yes
collapseNeutralToYes positiveEvidence = yes

negativeNeutralCollisionUnderNoCollapse :
  collapseNeutralToNo negativeEvidence
  ≡ collapseNeutralToNo neutralEvidence
negativeNeutralCollisionUnderNoCollapse = refl

neutralPositiveCollisionUnderYesCollapse :
  collapseNeutralToYes neutralEvidence
  ≡ collapseNeutralToYes positiveEvidence
neutralPositiveCollisionUnderYesCollapse = refl

record EpistemicSuspensionBoundary : Set where
  constructor epistemic-suspension-boundary
  field
    neutralMeansFalse : Bool
    neutralMeansFalseIsFalse : neutralMeansFalse ≡ false
    neutralMeansTrue : Bool
    neutralMeansTrueIsFalse : neutralMeansTrue ≡ false
    neutralRequiresFurtherResolution : Bool
    neutralRequiresFurtherResolutionIsTrue :
      neutralRequiresFurtherResolution ≡ true
    genericSuspensionIsIdenticalToMotifM5 : Bool
    genericSuspensionIsIdenticalToMotifM5IsFalse :
      genericSuspensionIsIdenticalToMotifM5 ≡ false

canonicalEpistemicSuspensionBoundary : EpistemicSuspensionBoundary
canonicalEpistemicSuspensionBoundary =
  epistemic-suspension-boundary
    false refl
    false refl
    true refl
    false refl
