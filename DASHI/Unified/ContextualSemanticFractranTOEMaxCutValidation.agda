module DASHI.Unified.ContextualSemanticFractranTOEMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.ContextualSemanticFractranTOEMaxCutExact as Exact
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.PNFHyperfabric as PNF

------------------------------------------------------------------------
-- Same-owner integration checks.
------------------------------------------------------------------------

toeReceiptMatchesOwner :
  TOE.toeContextualSemanticFractranMaxCutReceipt
  ≡ Exact.canonicalContextualSemanticFractranTOEMaxCutReceipt
toeReceiptMatchesOwner = refl

unifierReceiptMatchesOwner :
  Unifier.unifierContextualSemanticFractranMaxCutReceipt
  ≡ Exact.canonicalContextualSemanticFractranTOEMaxCutReceipt
unifierReceiptMatchesOwner = refl

pnfReceiptMatchesOwner :
  PNF.pnfContextualSemanticFractranMaxCutReceipt
  ≡ Exact.canonicalContextualSemanticFractranTOEMaxCutReceipt
pnfReceiptMatchesOwner = refl

------------------------------------------------------------------------
-- Fleet target scope remains the canonical 584 / 44 / 58 partition.
------------------------------------------------------------------------

dischargedFibreCountIs584 :
  Exact.fleetDischargedFibreCount ≡ 584
dischargedFibreCountIs584 =
  Exact.fleetDischargedFibreCountIs584

contradictionGapCountIs44 :
  Exact.fleetContradictionGapCount ≡ 44
contradictionGapCountIs44 =
  Exact.fleetContradictionGapCountIs44

targetFormalGapCountIs58 :
  Exact.fleetTargetFormalGapCount ≡ 58
targetFormalGapCountIs58 =
  Exact.fleetTargetFormalGapCountIs58

------------------------------------------------------------------------
-- Direct non-promotion remains reachable from both TOE roots.
------------------------------------------------------------------------

toeCoverageDoesNotCreateMonsterRepresentation :
  Exact.CoverageMonsterRepresentationPromotion → ⊥
toeCoverageDoesNotCreateMonsterRepresentation =
  TOE.toeContextualCoverageDoesNotCreateMonsterRepresentation

unifierCoverageDoesNotCreateMonsterRepresentation :
  Exact.CoverageMonsterRepresentationPromotion → ⊥
unifierCoverageDoesNotCreateMonsterRepresentation =
  Unifier.unifierContextualCoverageDoesNotCreateMonsterRepresentation

toeParetoChartDoesNotCreateMonsterRepresentation :
  Exact.ParetoTernaryMonsterRepresentationPromotion → ⊥
toeParetoChartDoesNotCreateMonsterRepresentation =
  TOE.toeContextualParetoChartDoesNotCreateMonsterRepresentation

unifierParetoChartDoesNotCreateMonsterRepresentation :
  Exact.ParetoTernaryMonsterRepresentationPromotion → ⊥
unifierParetoChartDoesNotCreateMonsterRepresentation =
  Unifier.unifierContextualParetoChartDoesNotCreateMonsterRepresentation

toeDischargedFibresRemainOutOfTarget :
  Exact.Fleet.FleetDischargedFibreRetargetPermission → ⊥
toeDischargedFibresRemainOutOfTarget =
  TOE.toeContextualFleetDischargedFibresRemainOutOfTarget

unifierDischargedFibresRemainOutOfTarget :
  Exact.Fleet.FleetDischargedFibreRetargetPermission → ⊥
unifierDischargedFibresRemainOutOfTarget =
  Unifier.unifierContextualFleetDischargedFibresRemainOutOfTarget
