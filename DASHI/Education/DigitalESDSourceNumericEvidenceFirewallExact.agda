{-# OPTIONS --safe #-}
module DASHI.Education.DigitalESDSourceNumericEvidenceFirewallExact where

------------------------------------------------------------------------
-- NUMERIC DATA ARE NOT A DEFAULT FOR UNREVIEWED ESD SOURCE CELLS.
-- Reuses the original source-dependent AccountedStudyWorld unchanged.
-- A numeric observation needs an actual directReviewed constructor,
-- a same-address equality, and a selected numeric value.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World

-- NFW00: The mask may denote missing numeric input, but cannot turn
-- pending source work, inaccessibility or other evidence statuses to 0.
data NumericPNFAt
  (scope : World.StudyWorldScope)
  (world : World.AccountedStudyWorld scope)
  (s : World.Study scope)
  (p : World.Part scope s)
  (a : World.Axis scope)
  (Value : Set) : Set₁ where

  measuredWithReview :
    (reviewed : World.ReviewedPartAxisEvidence scope s p a) →
    World.accounting world s p a ≡ World.directReviewed reviewed →
    (value : Value) →
    NumericPNFAt scope world s p a Value

  missingNumericInput :
    (originalStatus : World.PartAxisAccounting scope s p a) →
    originalStatus ≡ World.accounting world s p a →
    (missingReason : String) →
    NumericPNFAt scope world s p a Value

-- NFW01: Just a source metadata row or an unreviewed textual candidate
-- cannot inhabit the measured branch.  This is source-constructive:
-- a reviewer must separately supply the source audit evidence.
notAssessedCannotEqualDirectReviewed :
  {scope : World.StudyWorldScope} →
  {s : World.Study scope} →
  {p : World.Part scope s} →
  {a : World.Axis scope} →
  (work : String) →
  (reviewed : World.ReviewedPartAxisEvidence scope s p a) →
  World.notYetAssessed work ≡ World.directReviewed reviewed → ⊥
notAssessedCannotEqualDirectReviewed work reviewed ()

inaccessibleCannotEqualDirectReviewed :
  {scope : World.StudyWorldScope} →
  {s : World.Study scope} →
  {p : World.Part scope s} →
  {a : World.Axis scope} →
  (sourceRef accessRef : String) →
  (reviewed : World.ReviewedPartAxisEvidence scope s p a) →
  World.sourceInaccessible sourceRef accessRef ≡
  World.directReviewed reviewed → ⊥
inaccessibleCannotEqualDirectReviewed sourceRef accessRef reviewed ()

-- NFW02: A source's numeric view cannot modify any original
-- accounted world cell.  No source numeric scalar creates an evidence
-- review and no MP eigenmode receives truth authority here.

record NumericResearchCoordinate
  (scope : World.StudyWorldScope)
  (world : World.AccountedStudyWorld scope)
  (Value : Set) : Set₁ where
  constructor numeric-research-coordinate
  field
    position : World.StudyPart scope
    axis : World.Axis scope
    numeric :
      NumericPNFAt scope world
        (World.study position) (World.part position) axis Value

open NumericResearchCoordinate public
