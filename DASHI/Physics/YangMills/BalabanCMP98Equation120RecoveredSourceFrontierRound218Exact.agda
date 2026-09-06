{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation120RecoveredSourceFrontierRound218Exact where

------------------------------------------------------------------------
-- ROUND218 REPAIRED BIDI: RECOVERED SOURCE FRONTIER AFTER
-- R179/R181/R187/R189/R192.
--
-- R217 deliberately split the old opaque selected-semantics flag. Repository
-- archaeology shows that several coordinates are already paid or are not
-- required on the shortest route:
--
--   * R179: literal principal Y/Y_x index the Federbush family directly;
--            no identification equality exists or is needed.
--   * R181: the existing dyadic physical principal-log owner gives principal-
--            image admission directly; selected-cut-radius comparison is not
--            required on that route.
--   * R187 + R189: selected physical background -> exact unit-quaternion
--            periodic realization, with identity/multiply/inverse/path erasure
--            homomorphism proved.
--   * repaired R192: the actual physical side-13 background is represented in
--            the historical predecessor-indexed periodic API at n=12, with
--            suc 12 = 13.  The earlier n=13 specialization mixed side-14
--            historical geometry with side-13 physical data and is superseded.
--
-- What is NOT yet justified is constructing the selected variational/physical
-- background directly on the Path13 carrier.  Nor is the full perturbation
-- semantics closed: R147 uses one Vector both as the global Q' carrier and as
-- local R0 Lie values, while the physical Path13 perturbation is bond-indexed.
-- The surviving perturbation receipt therefore concerns the global Path13
-- field -> local oriented-bond Lie projection and scalar multiplication on that
-- same local Lie carrier.  It is NOT an identification with the unrelated
-- SFGC finite-action/IBP diagnostic fixture.
--
-- Thus the recovered source residual remains TWO independent coordinates,
-- with the periodic-realization coordinate pruned only through the repaired
-- n=12 -> side-13 owner.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119PrincipalYFederbushIndexRound179Exact as R179
import DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPhysicalStrongestProducerRound181Exact as R181
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187
import DASHI.Physics.YangMills.BalabanCMP98RawUnitPathHomomorphismRound189Exact as R189
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192

record Equation120RecoveredSourceResidual : Set₁ where
  field
    -- Construct the selected variational/physical background directly on the
    -- literal Path13 carrier (or an equivalent exact scale transport).
    Path13BackgroundIsSelectedPhysicalBackground : Set

    -- SAME A: the physical bond-indexed Path13 perturbation field must project
    -- to the local oriented-bond Lie values consumed by R147/R215, with the
    -- exact signed-link convention and scalar multiplication on that same Lie
    -- carrier.  The historical one-carrier API must not erase this distinction.
    PerturbationCoordinateSemantics : Set

open Equation120RecoveredSourceResidual public

principalYFederbushIndexAlreadyOwned : ProofLevel
principalYFederbushIndexAlreadyOwned =
  R179.cmp98Equation119PrincipalYFederbushIndexRound179Level

outerYFederbushIndexAlreadyOwned : ProofLevel
outerYFederbushIndexAlreadyOwned =
  R179.cmp98Equation119OuterYFederbushIndexRound179Level

selectedCutRadiusNotRequiredOnDyadicPhysicalRoute : ProofLevel
selectedCutRadiusNotRequiredOnDyadicPhysicalRoute =
  R181.cmp98Equation119DyadicPhysicalStrongestProducerRound181Level

selectedPhysicalPeriodicRealizationAlreadyOwned : ProofLevel
selectedPhysicalPeriodicRealizationAlreadyOwned =
  R187.cmp98SelectedPhysicalPeriodicRealizationRound187Level

rawUnitPathHomomorphismAlreadyOwned : ProofLevel
rawUnitPathHomomorphismAlreadyOwned =
  R189.cmp98RawUnitPathHolomorphismRound189Level

path13HistoricalPeriodicIndexRepairAlreadyOwned : ProofLevel
path13HistoricalPeriodicIndexRepairAlreadyOwned =
  R192.cmp98Path13PhysicalPeriodicIndexRepairRound192Level

path13PeriodicRealizationAlreadyOwned : ProofLevel
path13PeriodicRealizationAlreadyOwned =
  R192.cmp98Path13PhysicalPeriodicRealizationRound192Level

cmp98Equation120RecoveredSourceFrontierRound218Level : ProofLevel
cmp98Equation120RecoveredSourceFrontierRound218Level = machineChecked

cmp98PrincipalYFrontierPrunedRound218Level : ProofLevel
cmp98PrincipalYFrontierPrunedRound218Level = machineChecked

cmp98SelectedCutRadiusFrontierPrunedRound218Level : ProofLevel
cmp98SelectedCutRadiusFrontierPrunedRound218Level = machineChecked

cmp98PathRealizationFrontierPrunedRound218Level : ProofLevel
cmp98PathRealizationFrontierPrunedRound218Level =
  path13HistoricalPeriodicIndexRepairAlreadyOwned

literalCMP98Path13SelectedPhysicalBackgroundSameObjectRound218Level : ProofLevel
literalCMP98Path13SelectedPhysicalBackgroundSameObjectRound218Level = conditional

literalCMP98PerturbationCoordinateSemanticsRound218Level : ProofLevel
literalCMP98PerturbationCoordinateSemanticsRound218Level = conditional
