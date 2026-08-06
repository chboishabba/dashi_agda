module DASHI.Physics.Closure.NSTriadKNHessChildsTransportCommutatorSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Elias Hess-Childs; Matthew Rosenzweig; Sylvia Serfaty.
-- Title: "Another Look at Regularity in Transport-Commutator Estimates".
-- Comptes Rendus Mathematique 364 (2026).
-- DOI: 10.5802/crmath.837.
-- arXiv:2601.02326.
--
-- PURPOSE
-- Separate the recent Riesz/modulated-energy transport-commutator results
-- from the Littlewood--Paley block commutator used in the Luo terminal-shell
-- program.  The paper gives a genuine warning: a generic replacement of
-- Lipschitz control by BMO fails for its Riesz-type commutator, apart from a
-- special one-dimensional logarithmic endpoint, while almost-Lipschitz fields
-- lead to a defective estimate.
--
-- Those results constrain possible regularity shortcuts, but they do not
-- furnish the centered finite-frequency (L6,L3) estimate proved by the DASHI
-- Taylor/Bernstein lane.  This module records that logical boundary exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data TransportCommutatorSetting : Set where
  rieszModulatedEnergy : TransportCommutatorSetting
  dyadicLittlewoodPaleyBlock : TransportCommutatorSetting

sourceSetting : TransportCommutatorSetting
sourceSetting = rieszModulatedEnergy

sourceSettingIsNotDyadicBlock :
  sourceSetting ≢ dyadicLittlewoodPaleyBlock
sourceSettingIsNotDyadicBlock ()

data VelocityRegularityOutcome : Set where
  genericBMOReplacementFails : VelocityRegularityOutcome
  oneDimensionalLogEndpoint : VelocityRegularityOutcome
  almostLipschitzDefectiveEstimate : VelocityRegularityOutcome
  sixThreeCenteredGapEstimate : VelocityRegularityOutcome

sourceGenericOutcome : VelocityRegularityOutcome
sourceGenericOutcome = genericBMOReplacementFails

sourceDefectiveOutcome : VelocityRegularityOutcome
sourceDefectiveOutcome = almostLipschitzDefectiveEstimate

sourceDoesNotStateSixThreeGapEstimate :
  sourceGenericOutcome ≢ sixThreeCenteredGapEstimate
sourceDoesNotStateSixThreeGapEstimate ()

sourceDefectiveEstimateIsNotSixThreeGapEstimate :
  sourceDefectiveOutcome ≢ sixThreeCenteredGapEstimate
sourceDefectiveEstimateIsNotSixThreeGapEstimate ()
