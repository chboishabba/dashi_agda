module DASHI.Physics.YangMills.BalabanPhysicalC2CompletionLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
import DASHI.Physics.YangMills.BalabanPath4SU2CoarseFineSplittingExact
import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact
import DASHI.Physics.YangMills.BalabanPath4SU2TranslatedCoarsePropagatorExact
import DASHI.Physics.YangMills.BalabanPath4SU2BackgroundStabilityExact
import DASHI.Physics.YangMills.BalabanC2SmallLargeAllScaleExact

finiteSumFubiniClosureLevel : ProofLevel
finiteSumFubiniClosureLevel = machineChecked

sideFourAxisAverageClosureLevel : ProofLevel
sideFourAxisAverageClosureLevel = machineChecked

sideFourMartingaleOrthogonalityClosureLevel : ProofLevel
sideFourMartingaleOrthogonalityClosureLevel = machineChecked

concreteCoarseCarrierLevel : ProofLevel
concreteCoarseCarrierLevel = machineChecked

concreteQAdjointCoisometryLevel : ProofLevel
concreteQAdjointCoisometryLevel = machineChecked

concreteCoarseFinePythagorasLevel : ProofLevel
concreteCoarseFinePythagorasLevel = machineChecked

fineFluctuationCoercivityLevel : ProofLevel
fineFluctuationCoercivityLevel = machineChecked

configuredGaugeFixedOperatorLevel : ProofLevel
configuredGaugeFixedOperatorLevel = machineChecked

configuredPropagatorAssemblyLevel : ProofLevel
configuredPropagatorAssemblyLevel = machineChecked

translatedCoarsePropagatorCompatibilityLevel : ProofLevel
translatedCoarsePropagatorCompatibilityLevel = machineChecked

backgroundDifferenceAndNeumannAssemblyLevel : ProofLevel
backgroundDifferenceAndNeumannAssemblyLevel = machineChecked

smallLargeAllScaleAssemblyLevel : ProofLevel
smallLargeAllScaleAssemblyLevel = machineChecked

-- Standard finite-dimensional coercive inversion is the only imported linear
-- analysis authority in the configured side-four propagator layer.
finiteCoerciveInverseAuthorityLevel : ProofLevel
finiteCoerciveInverseAuthorityLevel = standardImported

-- These are the actual frontier estimates, not algebraic wiring:
-- background relative-form smallness, concrete large-field action/activity
-- suppression, and quantitative one-step preservation of the coercive domain.
backgroundRelativeFormProducerLevel : ProofLevel
backgroundRelativeFormProducerLevel = conditional

largeFieldSuppressionProducerLevel : ProofLevel
largeFieldSuppressionProducerLevel = conditional

oneStepPhysicalCoercivityTransferProducerLevel : ProofLevel
oneStepPhysicalCoercivityTransferProducerLevel = conditional

-- Set only after scripts/run_agda29_parallel_check.sh DASHI/Everything.agda
-- reaches the end of the complete module graph at this branch head.
branchHeadAuthoritativeAgda29TypecheckLevel : ProofLevel
branchHeadAuthoritativeAgda29TypecheckLevel = conditional
