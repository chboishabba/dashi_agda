module DASHI.Physics.YangMills.BalabanC1ExactLemmaAliases where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (ScalarBondField4)
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact as Hodge
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicOpenEnergySeamExact as Seam
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Bond

-- Requested audit name for the four-axis divergence-square expansion.
divergenceSquareExpansion : ∀ (field : ScalarBondField4) →
  Hodge.componentDivergenceEnergy field
  ≡ Hodge.componentDivergenceExpanded field
divergenceSquareExpansion = Hodge.componentDivergenceEnergyExpansion

-- Requested audit name for expansion of the literal axis/site difference fold.
componentDifferenceEnergyAxisSiteFold : ∀ (field : ScalarBondField4) →
  Hodge.componentPeriodicDifferenceEnergy field
  ≡ Hodge.componentPeriodicDifferenceExpanded field
componentDifferenceEnergyAxisSiteFold =
  Hodge.componentPeriodicDifferenceEnergyExpansion

-- The repository reference energy is the open-edge component fold.  The exact
-- periodic fold differs by the separately exposed wrap remainder.
componentDifferenceEnergyMatchesBondReferenceDifferenceEnergy :
  ∀ (field : ScalarBondField4) →
  Seam.componentOpenDifferenceEnergy field
  ≡ Bond.bondReferenceDifferenceEnergy field
componentDifferenceEnergyMatchesBondReferenceDifferenceEnergy =
  Seam.componentOpenDifferenceEnergyMatchesBondReferenceDifferenceEnergy

c1ExactLemmaAliasesLevel : ProofLevel
c1ExactLemmaAliasesLevel = machineChecked
