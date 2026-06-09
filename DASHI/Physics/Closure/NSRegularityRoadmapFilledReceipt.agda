module DASHI.Physics.Closure.NSRegularityRoadmapFilledReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayNSProofRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.NSRegularityGapReceipt as Gap

data NSRegularityRoadmapFilledStatus : Set where
  roadmapFilledWithOpenRegularityGap :
    NSRegularityRoadmapFilledStatus

data NSRegularityRoadmapMilestone : Set where
  weakSolutionBranchSeparated :
    NSRegularityRoadmapMilestone
  finiteEnergyAndEnstrophyRungsFilled :
    NSRegularityRoadmapMilestone
  finiteVorticityRungsFilled :
    NSRegularityRoadmapMilestone
  bkmUniformControlStillOpen :
    NSRegularityRoadmapMilestone
  clayRegularityStillOpen :
    NSRegularityRoadmapMilestone

canonicalNSRegularityRoadmapMilestones :
  List NSRegularityRoadmapMilestone
canonicalNSRegularityRoadmapMilestones =
  weakSolutionBranchSeparated
  ∷ finiteEnergyAndEnstrophyRungsFilled
  ∷ finiteVorticityRungsFilled
  ∷ bkmUniformControlStillOpen
  ∷ clayRegularityStillOpen
  ∷ []

nsRegularityRoadmapFilledStatement : String
nsRegularityRoadmapFilledStatement =
  "The NS roadmap is filled through finite-depth weak, energy, enstrophy, vorticity, and BKM rungs; the global smooth regularity and Clay branches remain open."

record NSRegularityRoadmapFilledReceipt : Setω where
  field
    status :
      NSRegularityRoadmapFilledStatus

    roadmapReceipt :
      Roadmap.ClayNSProofRoadmapReceipt

    roadmapWeakBranchSeparated :
      Roadmap.weakSolutionBranchSeparated roadmapReceipt ≡ true

    roadmapBKMBarrierRecorded :
      Roadmap.bkmBarrierRecorded roadmapReceipt ≡ true

    roadmapSmoothRegularityFalse :
      Roadmap.smoothGlobalRegularityProved roadmapReceipt ≡ false

    roadmapClayFalse :
      Roadmap.clayNavierStokesPromoted roadmapReceipt ≡ false

    regularityGapReceipt :
      Gap.NSRegularityGapReceipt

    gapFiniteDepthRungsTrue :
      Gap.finiteDepthRegularityRungsRecorded
        regularityGapReceipt
      ≡
      true

    gapGlobalSmoothFalse :
      Gap.globalSmoothRegularityProved regularityGapReceipt ≡ false

    gapClayFalse :
      Gap.clayNavierStokesPromoted regularityGapReceipt ≡ false

    milestones :
      List NSRegularityRoadmapMilestone

    milestonesAreCanonical :
      milestones ≡ canonicalNSRegularityRoadmapMilestones

    roadmapFilled :
      Bool

    roadmapFilledIsTrue :
      roadmapFilled ≡ true

    n1LocalSmoothnessCitationAuthorityRecorded :
      Bool

    n1LocalSmoothnessCitationAuthorityRecordedIsTrue :
      n1LocalSmoothnessCitationAuthorityRecorded ≡ true

    n2UniformEnstrophyPassageOpen :
      Bool

    n2UniformEnstrophyPassageOpenIsTrue :
      n2UniformEnstrophyPassageOpen ≡ true

    n3BKMCitationAuthorityRecorded :
      Bool

    n3BKMCitationAuthorityRecordedIsTrue :
      n3BKMCitationAuthorityRecorded ≡ true

    n4VorticityLinfinityControlOpen :
      Bool

    n4VorticityLinfinityControlOpenIsTrue :
      n4VorticityLinfinityControlOpen ≡ true

    criticalBesovNextTargetRecorded :
      Bool

    criticalBesovNextTargetRecordedIsTrue :
      criticalBesovNextTargetRecorded ≡ true

    lerayWeakSolutionBranchAvailable :
      Bool

    lerayWeakSolutionBranchAvailableIsTrue :
      lerayWeakSolutionBranchAvailable ≡ true

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ false

    vorticityControlClosed :
      Bool

    vorticityControlClosedIsFalse :
      vorticityControlClosed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsRegularityRoadmapFilledStatement

    receiptBoundary :
      List String

open NSRegularityRoadmapFilledReceipt public

canonicalNSRegularityRoadmapFilledReceipt :
  NSRegularityRoadmapFilledReceipt
canonicalNSRegularityRoadmapFilledReceipt =
  record
    { status =
        roadmapFilledWithOpenRegularityGap
    ; roadmapReceipt =
        Roadmap.canonicalClayNSProofRoadmapReceipt
    ; roadmapWeakBranchSeparated =
        refl
    ; roadmapBKMBarrierRecorded =
        refl
    ; roadmapSmoothRegularityFalse =
        refl
    ; roadmapClayFalse =
        refl
    ; regularityGapReceipt =
        Gap.canonicalNSRegularityGapReceipt
    ; gapFiniteDepthRungsTrue =
        refl
    ; gapGlobalSmoothFalse =
        refl
    ; gapClayFalse =
        refl
    ; milestones =
        canonicalNSRegularityRoadmapMilestones
    ; milestonesAreCanonical =
        refl
    ; roadmapFilled =
        true
    ; roadmapFilledIsTrue =
        refl
    ; n1LocalSmoothnessCitationAuthorityRecorded =
        true
    ; n1LocalSmoothnessCitationAuthorityRecordedIsTrue =
        refl
    ; n2UniformEnstrophyPassageOpen =
        true
    ; n2UniformEnstrophyPassageOpenIsTrue =
        refl
    ; n3BKMCitationAuthorityRecorded =
        true
    ; n3BKMCitationAuthorityRecordedIsTrue =
        refl
    ; n4VorticityLinfinityControlOpen =
        true
    ; n4VorticityLinfinityControlOpenIsTrue =
        refl
    ; criticalBesovNextTargetRecorded =
        true
    ; criticalBesovNextTargetRecordedIsTrue =
        refl
    ; lerayWeakSolutionBranchAvailable =
        true
    ; lerayWeakSolutionBranchAvailableIsTrue =
        refl
    ; globalSmoothRegularityProved =
        false
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; vorticityControlClosed =
        false
    ; vorticityControlClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsRegularityRoadmapFilledStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The roadmap is filled as a dependency ledger, not as a regularity proof"
        ∷ "N1 local smoothness and N3 BKM are citation authorities; N2 uniform enstrophy and N4 vorticity Linfinity remain open"
        ∷ "Critical Besov/vorticity control is the next named target"
        ∷ "The weak-solution branch is true while BKM/vorticity closure remains false"
        ∷ "Global smooth regularity and Clay promotion remain false"
        ∷ []
    }

nsRegularityRoadmapFilledKeepsClayFalse :
  clayNavierStokesPromoted
    canonicalNSRegularityRoadmapFilledReceipt
  ≡
  false
nsRegularityRoadmapFilledKeepsClayFalse =
  refl
