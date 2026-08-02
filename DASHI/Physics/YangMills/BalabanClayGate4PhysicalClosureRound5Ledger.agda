module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound5Ledger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneSplitFibreExact as CMP109
import DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneWeightExact as Weight
import DASHI.Physics.YangMills.BalabanClayGate4AlternatingTaylorEnvelopeExact as Taylor
import DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusFromSignedTailsExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4SeriesLipschitzAssemblyExact as Lipschitz
import DASHI.Physics.YangMills.BalabanClayGate4NewtonFourChannelQuarterExact as Newton
import DASHI.Physics.YangMills.BalabanClayGate4RationalWilsonQuadraticSecondDifferenceExact as WilsonHessian
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalFunctionalSecondVariationExact as Functional
import DASHI.Physics.YangMills.BalabanClayGate4SandwichOperatorToFormBoundExact as Sandwich
import DASHI.Physics.YangMills.BalabanClayGate4WilsonPlaquetteBadCubeBudgetExact as LargeField
import DASHI.Physics.YangMills.BalabanClayGate4GaugeCubicTaylorRemainderSumExact as Cubic
import DASHI.Physics.YangMills.BalabanClayGate4WeakeningProductSupportExact as Weakening
import DASHI.Physics.YangMills.BalabanClayGate4ConnectedTreeDecayExact as TreeDecay
import DASHI.Physics.YangMills.BalabanClayGate4DyadicGeometricRootedSummabilityExact as Rooted
import DASHI.Physics.YangMills.BalabanClayGate4DyadicRandomWalkTailExact as RandomWalk
import DASHI.Physics.YangMills.BalabanClayGate4FiveActivityTenthToHalfExact as Activity
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound5IntegratedExact as Integrated

------------------------------------------------------------------------
-- Round-five proof-level ledger. Exact arithmetic and finite/order-theoretic
-- consequences are machine checked. The remaining levels name only literal
-- local analytic estimates, never whole conclusions already derived above.
------------------------------------------------------------------------

cmp109RadiusOneSideAndVolumeLevel = CMP109.cmp109RadiusOneSideAndVolumeLevel
cmp109SplitProjectionFibreLevel = CMP109.cmp109SplitProjectionFibreLevel
cmp109SplitEndpointBlockLevel = CMP109.cmp109SplitEndpointBlockLevel
cmp109RadiusOnePhysicalDecisionLevel = CMP109.cmp109RadiusOnePhysicalDecisionLevel
cmp109RadiusOneRationalWeightLevel = Weight.cmp109RadiusOneRationalWeightLevel

alternatingTaylorEnvelopeLevel = Taylor.alternatingTaylorEnvelopeLevel
positiveTaylorTailEnvelopeLevel = Taylor.positiveTaylorTailEnvelopeLevel
su2HalfRadiusSignedTailConstructionLevel = SU2.su2HalfRadiusSignedTailConstructionLevel
su2HalfRadiusTaylorInequalitiesDerivedLevel = SU2.su2HalfRadiusTaylorInequalitiesDerivedLevel
finiteSeriesLipschitzAssemblyLevel = Lipschitz.finiteSeriesLipschitzAssemblyLevel
seriesLimitLipschitzPassageLevel = Lipschitz.seriesLimitLipschitzPassageLevel
newtonFourChannelQuarterArithmeticLevel = Newton.newtonFourChannelQuarterArithmeticLevel
federbushFaddeevPopovFourChannelReuseLevel = Newton.federbushFaddeevPopovFourChannelReuseLevel

wilsonAmbientParallelogramLevel = WilsonHessian.wilsonAmbientParallelogramLevel
wilsonQuadraticSecondDifferenceLevel = WilsonHessian.wilsonQuadraticSecondDifferenceLevel
physicalFunctionalSecondVariationLevel = Functional.physicalFunctionalSecondVariationLevel
physicalFunctionalFiveChannelOwnershipLevel = Functional.physicalFunctionalFiveChannelOwnershipLevel
sandwichOperatorNormProductLevel = Sandwich.sandwichOperatorNormProductLevel
sandwichUnitFormProductLevel = Sandwich.sandwichUnitFormProductLevel

wilsonPlaquetteBadCubePenaltyLevel = LargeField.wilsonPlaquetteBadCubePenaltyLevel
wilsonFiniteBadRegionBudgetLevel = LargeField.wilsonFiniteBadRegionBudgetLevel
gaugeCubicTaylorFiniteAssemblyLevel = Cubic.gaugeCubicTaylorFiniteAssemblyLevel
weakeningProductLocalInfluenceLevel = Weakening.weakeningProductLocalInfluenceLevel
connectedTreeEdgeDecayLevel = TreeDecay.connectedTreeEdgeDecayLevel
dyadicRootedExactTailIdentityLevel = Rooted.dyadicRootedExactTailIdentityLevel
dyadicRootedOrderClosureLevel = Rooted.dyadicRootedOrderClosureLevel
dyadicRandomWalkPartialMajorantLevel = RandomWalk.dyadicRandomWalkPartialMajorantLevel
dyadicRandomWalkDoubleAmplitudeLevel = RandomWalk.dyadicRandomWalkDoubleAmplitudeLevel
fiveActivityTenthArithmeticLevel = Activity.fiveActivityTenthArithmeticLevel
fiveActivityHalfAllocationLevel = Activity.fiveActivityHalfAllocationLevel

physicalClosureRound5IntegratedCarrierLevel = Integrated.physicalClosureRound5IntegratedCarrierLevel
physicalClosureRound5ConcreteCMP109Level = Integrated.physicalClosureRound5ConcreteCMP109Level
physicalClosureRound5SignedTailAndNewtonLevel = Integrated.physicalClosureRound5SignedTailAndNewtonLevel
physicalClosureRound5FunctionalAndPolymerLevel = Integrated.physicalClosureRound5FunctionalAndPolymerLevel

------------------------------------------------------------------------
-- Irreducible physical inhabitants after round five.
------------------------------------------------------------------------

physicalPeriodicTorusSplitFibreEquivalenceInputsLevel : ProofLevel
physicalPeriodicTorusSplitFibreEquivalenceInputsLevel = conditional

physicalBishopSignedTailInputsLevel = SU2.physicalBishopSignedTailInputsLevel
physicalBishopOrderClosedLimitInputsLevel = Lipschitz.physicalBishopOrderClosedLimitInputsLevel
physicalFederbushChannelEstimatesInputsLevel = Newton.physicalFederbushChannelEstimatesInputsLevel
physicalFaddeevPopovChannelEstimatesInputsLevel = Newton.physicalFaddeevPopovChannelEstimatesInputsLevel

physicalPlaquetteDerivativeChainRuleInputsLevel = WilsonHessian.physicalPlaquetteDerivativeChainRuleInputsLevel
physicalWilsonTransportChartDerivativeInputsLevel = Functional.physicalWilsonTransportChartDerivativeInputsLevel
physicalGaugeConstraintDerivativeInputsLevel = Functional.physicalGaugeConstraintDerivativeInputsLevel
physicalFiveChannelStageNormInputsLevel = Sandwich.physicalFiveChannelStageNormInputsLevel

physicalWilsonEntropyComparisonInputsLevel = LargeField.physicalWilsonEntropyComparisonInputsLevel
physicalGaugeLocalThirdDerivativeInputsLevel = Cubic.physicalGaugeLocalThirdDerivativeInputsLevel
physicalWeakeningLocalFactorSupportInputsLevel = Weakening.physicalWeakeningLocalFactorSupportInputsLevel
physicalConnectedActivityTreeRepresentationInputsLevel = TreeDecay.physicalConnectedActivityTreeRepresentationInputsLevel
physicalGaugeEdgeDecayInputsLevel = TreeDecay.physicalGaugeEdgeDecayInputsLevel
physicalRandomWalkDyadicShellInputsLevel = RandomWalk.physicalRandomWalkDyadicShellInputsLevel
physicalFiveActivityTenthEstimatesInputsLevel = Activity.physicalFiveActivityTenthEstimatesInputsLevel

physicalClosureRound5LedgerLevel : ProofLevel
physicalClosureRound5LedgerLevel = machineChecked
