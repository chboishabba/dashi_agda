{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayUrsellTransferMixingBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as KP
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact as Ursell
import DASHI.Physics.YangMills.YMClayCorrelationCriterionParityExact as Correlation

------------------------------------------------------------------------
-- Cross-pollination boundary: existing KP/Ursell machinery versus the new
-- literal-transfer correlation criterion.
--
-- Existing native Agda mathematics pays:
--
--   finite geometric KP shell arithmetic
--   + Ursell finite-tail/Cauchy assembly
--   + connected-correlation exponential decay
--
-- once an `InfiniteUrsellLimit` with its physical finite-crossing/tree-graph
-- input is supplied.
--
-- The new Lean donor criterion pays:
--
--   uniform joint-density mixing OR a state-uniform truncated correlation bound
--     -> literal two-slice transfer decorrelator.
--
-- These are NOT the same theorem.  A bound for selected/pairwise observables
-- does not by itself bound the transfer operator on every vacuum-orthogonal L2
-- state.  An explicit upgrade is required: for example a uniform density/TV
-- estimate for the full two-slice law, or a proved complete-basis extension
-- from observable bounds to the whole physical Hilbert carrier.
------------------------------------------------------------------------

pairwiseObservableUrsellDecayAvailableConditionally : Bool
pairwiseObservableUrsellDecayAvailableConditionally = true

pairwiseObservableUrsellDecayAvailableConditionallyIsTrue :
  pairwiseObservableUrsellDecayAvailableConditionally ≡ true
pairwiseObservableUrsellDecayAvailableConditionallyIsTrue = refl

pairwiseObservableUrsellDecayPaysUniformL2Mixing : Bool
pairwiseObservableUrsellDecayPaysUniformL2Mixing = false

pairwiseObservableUrsellDecayPaysUniformL2MixingIsFalse :
  pairwiseObservableUrsellDecayPaysUniformL2Mixing ≡ false
pairwiseObservableUrsellDecayPaysUniformL2MixingIsFalse = refl

physicalUrsellTreeGraphMajorantStillConditional : Bool
physicalUrsellTreeGraphMajorantStillConditional = true

physicalUrsellTreeGraphMajorantStillConditionalIsTrue :
  physicalUrsellTreeGraphMajorantStillConditional ≡ true
physicalUrsellTreeGraphMajorantStillConditionalIsTrue = refl

observableToUniformMixingUpgradeStillRequired : Bool
observableToUniformMixingUpgradeStillRequired = true

observableToUniformMixingUpgradeStillRequiredIsTrue :
  observableToUniformMixingUpgradeStillRequired ≡ true
observableToUniformMixingUpgradeStillRequiredIsTrue = refl

uniformJointDensityWouldCloseThisUpgrade : Bool
uniformJointDensityWouldCloseThisUpgrade = true

uniformJointDensityWouldCloseThisUpgradeIsTrue :
  uniformJointDensityWouldCloseThisUpgrade ≡ true
uniformJointDensityWouldCloseThisUpgradeIsTrue = refl

completeBasisOperatorNormUpgradeWouldAlsoCloseThisUpgrade : Bool
completeBasisOperatorNormUpgradeWouldAlsoCloseThisUpgrade = true

completeBasisOperatorNormUpgradeWouldAlsoCloseThisUpgradeIsTrue :
  completeBasisOperatorNormUpgradeWouldAlsoCloseThisUpgrade ≡ true
completeBasisOperatorNormUpgradeWouldAlsoCloseThisUpgradeIsTrue = refl

kpFiniteGeometricLevel : ProofLevel
kpFiniteGeometricLevel = KP.finiteTraceKoteckyPreissBoundLevel

ursellTailAssemblyLevel : ProofLevel
ursellTailAssemblyLevel = Ursell.infiniteConnectedCorrelationDecayAssemblyLevel

physicalUrsellMajorantLevel : ProofLevel
physicalUrsellMajorantLevel = Ursell.physicalUrsellTreeGraphMajorantLevel

uniformMixingCriterionLevel : ProofLevel
uniformMixingCriterionLevel = Correlation.correlationCriterionLeanLevel

interactingUniformMixingInputLevel : ProofLevel
interactingUniformMixingInputLevel = Correlation.interactingWilsonMixingInputLevel

data UrsellTransferMixingBoundaryPresent : Set where
  ursellTransferMixingBoundaryPresent : UrsellTransferMixingBoundaryPresent

ursellTransferMixingBoundaryWitness : UrsellTransferMixingBoundaryPresent
ursellTransferMixingBoundaryWitness = ursellTransferMixingBoundaryPresent
