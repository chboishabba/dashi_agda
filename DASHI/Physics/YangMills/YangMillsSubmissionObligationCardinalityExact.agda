module DASHI.Physics.YangMills.YangMillsSubmissionObligationCardinalityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact cardinality audit for the submission inventory.
--
-- The theorem-critical spine A--G contains 191 obligations:
--
--   58 Gate-4
-- + 56 local-lattice / Step-V
-- + 13 RG transfer
-- + 10 fixed-lattice gap
-- + 13 thermodynamic limit
-- + 20 cutoff removal / continuum
-- + 21 OS reconstruction / physical gap
-- = 191.
--
-- The additional foundational and gauge-structural sections H--I contain
-- 15 + 13 = 28 obligations.  Consequently the full A--I inventory contains
-- 219 obligations, not 191.  Keeping both totals explicit prevents the
-- theorem-spine count from being silently conflated with the complete
-- formal-submission count.
------------------------------------------------------------------------

gate4ObligationCount : ℕ
gate4ObligationCount = 58

localStepVObligationCount : ℕ
localStepVObligationCount = 56

rgTransferObligationCount : ℕ
rgTransferObligationCount = 13

fixedLatticeObligationCount : ℕ
fixedLatticeObligationCount = 10

thermodynamicObligationCount : ℕ
thermodynamicObligationCount = 13

continuumObligationCount : ℕ
continuumObligationCount = 20

osEndpointObligationCount : ℕ
osEndpointObligationCount = 21

foundationObligationCount : ℕ
foundationObligationCount = 15

gaugeStructuralObligationCount : ℕ
gaugeStructuralObligationCount = 13

theoremSpineObligationCount : ℕ
theoremSpineObligationCount =
  gate4ObligationCount
  + localStepVObligationCount
  + rgTransferObligationCount
  + fixedLatticeObligationCount
  + thermodynamicObligationCount
  + continuumObligationCount
  + osEndpointObligationCount

additionalFormalisationObligationCount : ℕ
additionalFormalisationObligationCount =
  foundationObligationCount + gaugeStructuralObligationCount

fullSubmissionObligationCount : ℕ
fullSubmissionObligationCount =
  theoremSpineObligationCount + additionalFormalisationObligationCount

theoremSpineObligationCountExact :
  theoremSpineObligationCount ≡ 191
theoremSpineObligationCountExact = refl

additionalFormalisationObligationCountExact :
  additionalFormalisationObligationCount ≡ 28
additionalFormalisationObligationCountExact = refl

fullSubmissionObligationCountExact :
  fullSubmissionObligationCount ≡ 219
fullSubmissionObligationCountExact = refl

submissionObligationCardinalityLevel : ProofLevel
submissionObligationCardinalityLevel = machineChecked
