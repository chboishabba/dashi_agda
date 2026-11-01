module DASHI.Physics.YangMills.BalabanSelectedRegionSignedG2MasterExact where

------------------------------------------------------------------------
-- ROUND64 MASTER THEOREM 1: SIGNED SELECTED-REGION G2 ABSORPTION
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- The old implementation frontier exposed two estimates
--
--   R1-G11       <= a Q,
--   R2+R3+R4     <= b Q.
--
-- They are useful proof decomposition, but they are NOT two independent
-- mathematical endgame theorems.  The theorem actually consumed by the next
-- stage is one signed estimate on the exact correlated residual:
--
--   R_corr <= (55 / 18874368) Q.
--
-- This file makes that output the master producer.  The existing split
-- compiler is proved to instantiate the master interface, while future work is
-- free to prove the signed estimate directly and retain any cancellation that
-- the split would destroy.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as Blocks
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanChargeRelativeCorrelatedD1G2ClosureExact as Split

record SignedSelectedRegionG2Master
    (Configuration Multiplier : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    pseudoDataAt : Configuration →
      Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationAt : Configuration → KKT.StateVector
    bondFieldAt : Configuration → Physical.PhysicalSU2BondField4
    plaquetteAt : Configuration → Plaquette.Plaquette4

    canonicalInputsAt : ∀ configuration →
      Canonical.CanonicalSubsetCorrelatedAuthorityInputs
        (pseudoDataAt configuration)
        (firstVariationAt configuration)
        (bondFieldAt configuration)
        (plaquetteAt configuration)

    chargeAt : Configuration → ℚ

    signedResidualAbsorbed : ∀ configuration →
      InCertifiedRegion configuration →
      Ownership.correlatedResidualTotal
        (Blocks.canonicalFamily (canonicalInputsAt configuration))
      ≤ Selector.remainingSingletonCoefficient * chargeAt configuration

open SignedSelectedRegionG2Master public

selectedMinimizerSignedG2Absorbed :
  ∀ {Configuration Multiplier}
    (master : SignedSelectedRegionG2Master Configuration Multiplier) →
  Ownership.correlatedResidualTotal
    (Blocks.canonicalFamily
      (canonicalInputsAt master (selectedMinimizer master)))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt master (selectedMinimizer master)
selectedMinimizerSignedG2Absorbed master =
  signedResidualAbsorbed master
    (selectedMinimizer master)
    (selectedMinimizerInRegion master)

------------------------------------------------------------------------
-- Backwards compatibility theorem.
--
-- The former two-leaf package inhabits the new one-leaf master interface.
-- This is the formal reason the Round63 count 13 is implementation-shaped.
------------------------------------------------------------------------

masterFromSplitHeadroom :
  ∀ {Configuration Multiplier}
    (dataSet : Split.ChargeRelativeCorrelatedD1G2Data
      Configuration Multiplier) →
    Split.CorrelatedD1G2Headroom
      dataSet Selector.remainingSingletonCoefficient →
  SignedSelectedRegionG2Master Configuration Multiplier
masterFromSplitHeadroom dataSet headroom = record
  { InCertifiedRegion = Split.InCertifiedRegion dataSet
  ; selectedMinimizer = Split.selectedMinimizer dataSet
  ; selectedMinimizerInRegion = Split.selectedMinimizerInRegion dataSet
  ; pseudoDataAt = Split.pseudoDataAt dataSet
  ; firstVariationAt = Split.firstVariationAt dataSet
  ; bondFieldAt = Split.bondFieldAt dataSet
  ; plaquetteAt = Split.plaquetteAt dataSet
  ; canonicalInputsAt = Split.canonicalInputsAt dataSet
  ; chargeAt = Split.chargeAt dataSet
  ; signedResidualAbsorbed =
      Split.regionG2ClosesFromHeadroom dataSet headroom
  }

signedG2MasterCompilerLevel : ProofLevel
signedG2MasterCompilerLevel = machineChecked

-- The genuinely open theorem is now exactly one physical statement: construct
-- SignedSelectedRegionG2Master directly on the literal selected-background
-- carrier.  The split D1/higher-degree proof remains an available sufficient
-- route, not part of the final theorem count.
physicalSignedSelectedRegionG2MasterLevel : ProofLevel
physicalSignedSelectedRegionG2MasterLevel = conditional
