module DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintTangentProjectorBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- The generic projector formula
--
--      Pi = I - L^* (L L^*)^-1 L
--
-- is correct on any stratum/carrier where the supplied raw combined Gram is
-- actually invertible.  But the selected 780-row carrier is NOT such a carrier
-- at the flat background: the machine-checked constant-gauge multiplier
-- witness lies in its kernel.
--
-- This module records the exact boundary so the conditional projector theorem
-- cannot be promoted as a universal Gate-I construction.  The live physical
-- route is a based/reduced multiplier carrier, or an equivalent quotient-aware
-- normal projector that removes this redundancy before inversion.
------------------------------------------------------------------------

open import Relation.Nullary.Negation.Core using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintTangentProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRawGramNoGoExact as NoGo

selectedFlatRawCombinedGramInverseImpossible :
  ∀ site → ¬ Projector.FullGramInverseCertificate Physical.identityBackground
selectedFlatRawCombinedGramInverseImpossible =
  NoGo.rawCombinedFlatGramHasNoTwoSidedInverse

selectedFullRawGramProjectorNotUniversalLevel : ProofLevel
selectedFullRawGramProjectorNotUniversalLevel = machineChecked

selectedReducedOrBasedProjectorStillRequiredLevel : ProofLevel
selectedReducedOrBasedProjectorStillRequiredLevel = conditional
