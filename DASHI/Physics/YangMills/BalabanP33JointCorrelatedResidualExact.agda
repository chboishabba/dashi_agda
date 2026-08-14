module DASHI.Physics.YangMills.BalabanP33JointCorrelatedResidualExact where

-- Bałaban, "The Variational Problem and Background Fields in Renormalization
-- Group Method for Lattice Gauge Theories", CMP 102 (1985).
-- DOI: 10.1007/BF01229381.

open import Data.Rational.Base as ℚ using (ℚ; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as O
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualBoundsExact as B

jointResidual : O.CorrelatedResidualFamily → ℚ
jointResidual f = B.rawLocalizationSpillover f + B.selectedMultiplierDefectContribution f

jointResidualIsPhysicalTotal : ∀ {f} →
  O.ExactCorrelatedCancellation f →
  O.correlatedResidualTotal f ≡ jointResidual f
jointResidualIsPhysicalTotal = B.selectedCorrelatedResidualAtomCancellationExact

p33JointCorrelatedResidualLevel : ProofLevel
p33JointCorrelatedResidualLevel = machineChecked
