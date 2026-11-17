module DASHI.Physics.YangMills.BalabanC1ExactLemmaAliases where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (ScalarBondField4)
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact as Hodge
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicOpenEnergySeamExact as Seam
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Bond

-- Requested audit name for the four-axis divergence-square expansion.
divergenceSquareExpansion : ∀ (fld : ScalarBondField4) →
  Hodge.componentDivergenceEnergy fld
  ≡ Hodge.componentDivergenceExpanded fld
divergenceSquareExpansion = Hodge.componentDivergenceEnergyExpansion

-- Requested audit name for expansion of the literal axis/site difference fold.
componentDifferenceEnergyAxisSiteFold : ∀ (fld : ScalarBondField4) →
  Hodge.componentPeriodicDifferenceEnergy fld
  ≡ Hodge.componentPeriodicDifferenceExpanded fld
componentDifferenceEnergyAxisSiteFold =
  Hodge.componentPeriodicDifferenceEnergyExpansion

-- The repository reference energy is the open-edge component fold.  The exact
-- periodic fold differs by the separately exposed wrap remainder.
componentDifferenceEnergyMatchesBondReferenceDifferenceEnergy :
  ∀ (fld : Bond.RationalBondField4) →
  Seam.componentOpenDifferenceEnergy (Bond.bondComponent fld)
  ≡ Bond.bondReferenceDifferenceEnergy fld
componentDifferenceEnergyMatchesBondReferenceDifferenceEnergy =
  Seam.componentOpenDifferenceEnergyMatchesBondReferenceDifferenceEnergy

c1ExactLemmaAliasesLevel : ProofLevel
c1ExactLemmaAliasesLevel = machineChecked
