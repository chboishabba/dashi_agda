module DASHI.Physics.YangMills.YMClayOSLiteralStressRouteParetoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSLiteralSchwingerWeldRound127Exact as R127
import DASHI.Physics.YangMills.YangMillsClayStressOPERequirementBoundaryExact as Stress
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YMClayPhysicalStressOSCommonCoreWitnessExact as Strong
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as L2Recovery
import DASHI.Physics.YangMills.YMClayLevel2StressOPEMinCutExact as L2

------------------------------------------------------------------------
-- CLAY / OS / STRESS ROUTE PARETO
--
-- Three different theorem strengths must not be conflated.
--
-- LEVEL 1  physical OS mass-gap endpoint
--   source/continuum/OS application -> reconstructed Hamiltonian with gap.
--
-- LEVEL 2  literal Clay local-QFT stress/OPE endpoint
--   LEVEL 1 plus:
--     * R127: source OS Schwinger system = literal Clay Schwinger family;
--     * stress tensor on that SAME literal Schwinger family;
--     * physical OPE coefficients and remainders.
--
-- LEVEL 3  stronger local-generator theorem
--   LEVEL 2 plus stress Ward/local charge/common-core closure data
--   -> stress generator = H_OS -> same Stone evolution.
--
-- Level 3 is valuable but is NOT consumed by the literal
-- stressTensorAndOperatorProductExpansion Clay postcondition.
--
-- IMPORTANT TRUST BOUNDARY
--
-- This owner intentionally does not import
-- DASHI.Physics.QFT.StressEnergyBridgeReceiptSurface: that module is a generic
-- target/socket surface with postulated AQFT stress targets.  Its vocabulary
-- may guide future GR adapters, but it is not a theorem donor to this YM cone.
------------------------------------------------------------------------

record LiteralClayOSStressInputs
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    osLiteralWeld : R127.OSLiteralSchwingerWeld Y group
    stressOPEEvidence : Stress.LiteralClayStressOPEEvidence Y

open LiteralClayOSStressInputs public

literalClayStressOPEPostcondition :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C} →
  LiteralClayOSStressInputs Y group →
  Top.postconditionRequirement Y Clay.stressTensorAndOperatorProductExpansion group
literalClayStressOPEPostcondition {Y = Y} {group = group} inputs =
  Stress.literalStressOPEEvidenceIsClayPostcondition
    Y (stressOPEEvidence inputs) group


------------------------------------------------------------------------
-- Level-2 compression through the existing R126-R129 / Round87 chain.
------------------------------------------------------------------------

r127IndependentAfterR129Recovery : Bool
r127IndependentAfterR129Recovery = L2Recovery.r127IndependentAfterR129Recovery

r129PaysLiteralStressDerivative : Bool
r129PaysLiteralStressDerivative =
  L2.r129RecoveryPaysR127AndStressDerivative

dyadicOPERemainderDecayIndependentPhysicalLeaf : Bool
dyadicOPERemainderDecayIndependentPhysicalLeaf =
  L2.dyadicOPERemainderDecayIndependentAfterCompositeTailIdentification

allDepthOPECoefficientEqualityIndependentPhysicalLeaf : Bool
allDepthOPECoefficientEqualityIndependentPhysicalLeaf =
  L2.allDepthOPECoefficientEqualityIndependentAfterOneStepLaw

level2SameFamilyRecoveryLevel : ProofLevel
level2SameFamilyRecoveryLevel = L2.physicalR129RecoveryLevel

level2ShortDistanceOPEStressAFLevel : ProofLevel
level2ShortDistanceOPEStressAFLevel = L2.physicalRound87DLevel

------------------------------------------------------------------------
-- Exact route classification.
------------------------------------------------------------------------

osReconstructionMachineryMissing : Bool
osReconstructionMachineryMissing = false

osReconstructionMachineryMissingIsFalse :
  osReconstructionMachineryMissing ≡ false
osReconstructionMachineryMissingIsFalse = refl

osLiteralSameFamilyWeldStillPhysical : Bool
osLiteralSameFamilyWeldStillPhysical = true

osLiteralSameFamilyWeldStillPhysicalIsTrue :
  osLiteralSameFamilyWeldStillPhysical ≡ true
osLiteralSameFamilyWeldStillPhysicalIsTrue = refl

stressChargeEqualsOSHamiltonianMandatoryForLiteralClayStressOPE : Bool
stressChargeEqualsOSHamiltonianMandatoryForLiteralClayStressOPE = false

stressChargeEqualsOSHamiltonianMandatoryForLiteralClayStressOPEIsFalse :
  stressChargeEqualsOSHamiltonianMandatoryForLiteralClayStressOPE ≡ false
stressChargeEqualsOSHamiltonianMandatoryForLiteralClayStressOPEIsFalse = refl

commonCoreClosureMandatoryForLiteralClayStressOPE : Bool
commonCoreClosureMandatoryForLiteralClayStressOPE = false

commonCoreClosureMandatoryForLiteralClayStressOPEIsFalse :
  commonCoreClosureMandatoryForLiteralClayStressOPE ≡ false
commonCoreClosureMandatoryForLiteralClayStressOPEIsFalse = refl

stoneEvolutionEqualityMandatoryForLiteralClayStressOPE : Bool
stoneEvolutionEqualityMandatoryForLiteralClayStressOPE = false

stoneEvolutionEqualityMandatoryForLiteralClayStressOPEIsFalse :
  stoneEvolutionEqualityMandatoryForLiteralClayStressOPE ≡ false
stoneEvolutionEqualityMandatoryForLiteralClayStressOPEIsFalse = refl

samePhysicalStressConstructorCanFeedStrongerGeneratorTheorem : Bool
samePhysicalStressConstructorCanFeedStrongerGeneratorTheorem = true

samePhysicalStressConstructorCanFeedStrongerGeneratorTheoremIsTrue :
  samePhysicalStressConstructorCanFeedStrongerGeneratorTheorem ≡ true
samePhysicalStressConstructorCanFeedStrongerGeneratorTheoremIsTrue = refl

r127WeldCompilerLevel : ProofLevel
r127WeldCompilerLevel = R127.osLiteralSchwingerWeldCompilerLevel

r127PhysicalSameFamilyLevel : ProofLevel
r127PhysicalSameFamilyLevel = R127.literalBalabanOSSystemIsClaySchwingerLevel

literalClayStressOPECompilerLevel : ProofLevel
literalClayStressOPECompilerLevel = Stress.literalClayStressOPEBoundaryLevel

strongerStressGeneratorLevel : ProofLevel
strongerStressGeneratorLevel = Strong.physicalStressOSCommonCoreLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
