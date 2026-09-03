{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation120RecoveredSourceFrontierRound218Exact where

------------------------------------------------------------------------
-- ROUND218 BIDI: RECOVERED SOURCE FRONTIER AFTER R179/R181/R187/R189/R192.
--
-- R217 deliberately split the old opaque selected-semantics flag. Repository
-- archaeology then shows that several coordinates are already paid or are not
-- required on the shortest route:
--
--   * R179: literal principal Y/Y_x index the Federbush family directly;
--            no identification equality exists or is needed.
--   * R181: the existing dyadic physical principal-log owner gives principal-
--            image admission directly; the selected-cut-radius comparison is
--            not required on that route.
--   * R187 + R189: selected physical background -> exact unit-quaternion
--            periodic realization, with identity/multiply/inverse/path erasure
--            homomorphism proved.
--   * R192: the actual Path13 background has its own exact side-13 periodic
--            realization by construction.
--
-- What is NOT yet justified is silently identifying the R192 Path13 background
-- with the selected variational/physical background used by the R185/R187 lane.
-- Nor did repository search find an inhabitant of R147's perturbation
-- `bondComponent` / scalar-action projection fields.
--
-- Thus the source residual is now exactly TWO independent coordinates.
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
    -- SAME BONDS: the Path13 physical background selected by the source lane
    -- must be the selected variational/physical background whose estimates and
    -- chart semantics are consumed downstream.  This is a same-object receipt,
    -- not merely equality of carrier types or matching bounds.
    Path13BackgroundIsSelectedPhysicalBackground : Set

    -- SAME A: R147/R215's global perturbation vector -> oriented-bond component
    -- and scalar action must be the literal physical perturbation coordinates
    -- used by the selected finite Yang-Mills action/IBP lane.
    PerturbationCoordinateSemantics : Set

open Equation120RecoveredSourceResidual public

-- Archaeology receipts: these proof-level facts are imported from actual
-- theorem owners and therefore should not be reopened as new source leaves.
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
cmp98PathRealizationFrontierPrunedRound218Level = machineChecked

-- The only two source-facing physical receipts retained after the BIDI pass.
literalCMP98Path13SelectedPhysicalBackgroundSameObjectRound218Level : ProofLevel
literalCMP98Path13SelectedPhysicalBackgroundSameObjectRound218Level = conditional

literalCMP98PerturbationCoordinateSemanticsRound218Level : ProofLevel
literalCMP98PerturbationCoordinateSemanticsRound218Level = conditional
