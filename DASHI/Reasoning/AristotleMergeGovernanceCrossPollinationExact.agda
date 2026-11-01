module DASHI.Reasoning.AristotleMergeGovernanceCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GovernedObservationProvenanceExact as Lineage
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Reasoning.AristotleBranchMergeExact as Merge

------------------------------------------------------------------------
-- GOVERNANCE WELD FOR ARISTOTLE BRANCH MERGE
--
-- Two already-canonical DASHI constraints become actual merge obligations:
--
--   * coordinate lineage: erase -> later add is introduced, not inherited;
--   * least privilege: a structurally compatible branch merge does not itself
--     admit the resulting theorem route for elaboration/promotion.
------------------------------------------------------------------------

lineageOf : Merge.ProvenanceCode → Lineage.CoordinateLineage
lineageOf Merge.inheritedHistory = Lineage.inheritedCoordinate
lineageOf Merge.introducedHistory = Lineage.introducedCoordinate

eraseThenAddProducesIntroducedMergeLineage :
  Lineage.applyTwoEffects
    Lineage.erasesCoordinate
    Lineage.addsCoordinate
    Lineage.inheritedCoordinate
  ≡ lineageOf Merge.introducedHistory
eraseThenAddProducesIntroducedMergeLineage =
  Lineage.additionAfterErasureIsIntroducedNotInherited

eraseThenAddCannotAuthorizeInheritedMergeLineage :
  Lineage.applyTwoEffects
    Lineage.erasesCoordinate
    Lineage.addsCoordinate
    Lineage.inheritedCoordinate
  ≡ lineageOf Merge.inheritedHistory →
  ⊥
eraseThenAddCannotAuthorizeInheritedMergeLineage =
  Lineage.additionAfterErasureDoesNotRestoreInheritedLineage

------------------------------------------------------------------------
-- Structural merge compatibility and proof-route admission are independent
-- proof obligations.  A consumer that wants both must carry both receipts.
------------------------------------------------------------------------

record AdmittedGuardedMerge
    {Visible Dependency Provenance Item : Set}
    (left right : Merge.BranchSnapshot Visible Dependency Provenance Item) : Set₁ where
  constructor admittedGuardedMerge
  field
    mergeGuard : Merge.MergeGuard left right
    routeAdmission : Least.RouteAdmission
    admissionReference : String

open AdmittedGuardedMerge public

admittedMergeSnapshot :
  ∀ {Visible Dependency Provenance Item : Set}
    {left right : Merge.BranchSnapshot Visible Dependency Provenance Item} →
  AdmittedGuardedMerge left right →
  Merge.BranchSnapshot Visible Dependency Provenance Item
admittedMergeSnapshot receipt =
  Merge.guardedMerge (mergeGuard receipt)

admittedMergeLiveRoute :
  ∀ {Visible Dependency Provenance Item : Set}
    {left right : Merge.BranchSnapshot Visible Dependency Provenance Item} →
  AdmittedGuardedMerge left right →
  Least.LiveProofSearch
admittedMergeLiveRoute receipt =
  Least.elaborateRoute (routeAdmission receipt)

canonicalAdmittedCompatibleMerge :
  AdmittedGuardedMerge Merge.leftBranch Merge.compatibleRightBranch
canonicalAdmittedCompatibleMerge =
  admittedGuardedMerge
    Merge.canonicalCompatibleGuard
    Least.canonicalRouteAdmission
    "compatible branch reconciliation plus independent least-privilege route admission"

canonicalAdmittedMergeKeepsLemmaA :
  Merge.Knows
    (Merge.provedKnowledge
      (admittedMergeSnapshot canonicalAdmittedCompatibleMerge))
    Merge.lemmaA
canonicalAdmittedMergeKeepsLemmaA = inj₁ tt

canonicalAdmittedMergeKeepsLemmaB :
  Merge.Knows
    (Merge.provedKnowledge
      (admittedMergeSnapshot canonicalAdmittedCompatibleMerge))
    Merge.lemmaB
canonicalAdmittedMergeKeepsLemmaB = inj₂ tt

canonicalAdmittedMergeHasLiveRoute : Least.LiveProofSearch
canonicalAdmittedMergeHasLiveRoute =
  admittedMergeLiveRoute canonicalAdmittedCompatibleMerge

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AristotleMergeGovernanceBoundary : Set where
  constructor aristotleMergeGovernanceBoundary
  field
    laterReintroducedProvenanceCountsAsInherited : Bool
    laterReintroducedProvenanceCountsAsInheritedIsFalse :
      laterReintroducedProvenanceCountsAsInherited ≡ false

    mergeGuardAutomaticallySuppliesRouteAdmission : Bool
    mergeGuardAutomaticallySuppliesRouteAdmissionIsFalse :
      mergeGuardAutomaticallySuppliesRouteAdmission ≡ false

    admittedMergeMayRequireBothCompatibilityAndLeastPrivilege : Bool
    admittedMergeMayRequireBothCompatibilityAndLeastPrivilegeIsTrue :
      admittedMergeMayRequireBothCompatibilityAndLeastPrivilege ≡ true

    reading : String

canonicalAristotleMergeGovernanceBoundary : AristotleMergeGovernanceBoundary
canonicalAristotleMergeGovernanceBoundary =
  aristotleMergeGovernanceBoundary
    false refl
    false refl
    true refl
    "Aristotle branch reconciliation is governed independently by lineage compatibility and proof-route admission: later-added provenance is not restored inherited history, and a merge guard is not a least-privilege admission receipt."
