module DASHI.Interop.JPlusOne369FibreCarryHyperformalismExact where

------------------------------------------------------------------------
-- 369 / J+1 / CARRY / FIBRE / MOONSHINE CROSS-POLLINATION
--
-- This module does not identify the domains.  It extracts the exact common
-- mathematical shapes already present in-repo:
--
--   * 3*3 = 9, 9^2 = 81, 3*3*3 = 27 as address/weave geometry;
--   * typed 3/6/9 depth-phase fibres with canonical 6 -> 9 -> 3 forgetting;
--   * j+1 as a typed successor/rechart;
--   * balanced-ternary carry retaining a lower-level residue as memory while
--     moving a +1 contribution to the next depth;
--   * McKay's 196883 + 1 = 196884 as a separate exact fresh-unit extension;
--   * residual/gluing failure as a possible trigger for rechart rather than
--     deletion of the lower-level state;
--   * braid/fabric/hyperfabric as shared carrier vocabulary with attribution,
--     not a theorem that all semantic domains are equal.
--
-- Source calibration for the Moonshine arithmetic already used by the repo:
-- John H. Conway and Simon P. Norton, "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308-339.
-- DOI: 10.1112/blms/11.3.308.
-- Richard E. Borcherds, "Monstrous Moonshine and Monstrous Lie
-- Superalgebras", Inventiones Mathematicae 109 (1992), 405-444.
-- DOI: 10.1007/BF01232032.
--
-- Tesla boundary: periodic/polyphase engineering is allowed as historical
-- motivation only.  The repo explicitly blocks attribution of Base369,
-- p-adic towers, character/MDL machinery or modular/Monster mathematics to
-- Tesla.  No unsupported Tesla 3-6-9 doctrine is promoted here.
--
-- Braid/fabric vocabulary attribution follows the existing repo's Robin Wall
-- Kimmerer / Braiding Sweetgrass carrier attribution; it is cultural/narrative
-- provenance, not mathematical authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Interop.PNFHyperfabric369 as H369
import DASHI.Foundations.JChartSuccessorBoundary as Chart
import DASHI.Foundations.JPlusOneScaleBridge as J1
import DASHI.Foundations.SSPPrimeLane369Refinement as Ref369
import DASHI.Dynamics.TriadicResidualRechartDynamics as Rechart
import DASHI.Reasoning.CarryMemorySubvoxelReceipt as Carry
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel369
import DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary as Tesla
import DASHI.Interop.SweetgrassCarrierSpine as Sweetgrass
import Moonshine as Moon

------------------------------------------------------------------------
-- Exact arithmetic/address receipts.
------------------------------------------------------------------------

threeByThreeIsNine : H369.nonaryDimension ≡ 9
threeByThreeIsNine = H369.nonaryDimensionIsNine

nineSquaredIsEightyOne : H369.twoInteractionFabricDimension ≡ 81
nineSquaredIsEightyOne = H369.twoInteractionFabricDimensionIsEightyOne

threeCubedAddressIsTwentySeven :
  H369.dialecticDiscussionAtomDimension ≡ 27
threeCubedAddressIsTwentySeven =
  H369.dialecticDiscussionAtomDimensionIsTwentySeven

canonical369AddressDigits :
  Ref369.addressDigits Ref369.canonicalThreeSixNineAddress
  ≡ Ref369.digit-3 ∷ Ref369.digit-6 ∷ Ref369.digit-9 ∷ []
canonical369AddressDigits = Ref369.canonicalThreeSixNineDigits

canonical369PrefixKeepsThreeSixHistory :
  Ref369.prefixDigits Ref369.canonicalThreeSixNineAddress
  ≡ Ref369.digit-3 ∷ Ref369.digit-6 ∷ []
canonical369PrefixKeepsThreeSixHistory = Ref369.canonicalThreeSixNinePrefixDigits

------------------------------------------------------------------------
-- Stronger typed 3/6/9 fibre result already present in the depth-wheel lane.
--
--   3 = depth phase
--   6 = polar trit x depth phase
--   9 = full trit x depth phase
--
-- The canonical information direction is 6 -> 9 -> 3.  A canonical 9 -> 6
-- retraction needs an extra policy for the zero trit and is therefore blocked.
------------------------------------------------------------------------

threePhaseAtlasHasThreeCells :
  Wheel369.listLength Wheel369.depthPhaseAtlas ≡ Ref369.three
threePhaseAtlasHasThreeCells = Wheel369.depthPhaseAtlasCount

polarPhaseAtlasHasSixCells :
  Wheel369.listLength Wheel369.polarPhaseAtlas ≡ Ref369.six
polarPhaseAtlasHasSixCells = Wheel369.polarPhaseAtlasCount

fullPhaseAtlasHasNineCells :
  Wheel369.listLength Wheel369.fullPhaseAtlas ≡ Ref369.nine
fullPhaseAtlasHasNineCells = Wheel369.fullPhaseAtlasCount

polarEmbeddingPreservesDepthPhase :
  (cell : Wheel369.PolarPhaseCell) →
  Wheel369.forgetFullState (Wheel369.embedPolarPhaseCell cell)
  ≡ Wheel369.forgetPolarState cell
polarEmbeddingPreservesDepthPhase =
  Wheel369.polarEmbeddingPreservesDepthPhase

fullNineHasNoCanonicalRetractionToPolarSixWithoutZeroPolicy :
  Wheel369.DepthWheelBoundary.fullNineHasCanonicalRetractionToPolarSixWithoutZeroPolicy
    Wheel369.canonicalDepthWheelBoundary
  ≡ false
fullNineHasNoCanonicalRetractionToPolarSixWithoutZeroPolicy =
  Wheel369.DepthWheelBoundary.fullNineHasCanonicalRetractionToPolarSixWithoutZeroPolicyIsFalse
    Wheel369.canonicalDepthWheelBoundary

threeSixNineDepthPhaseReturnsToZero :
  Wheel369.depthWheelPhase 9 ≡ Wheel369.phase-0
threeSixNineDepthPhaseReturnsToZero = Wheel369.nineDepthPhaseIsZero

mckayFreshUnitExact : Moon.rep-dim + 1 ≡ Moon.j-coefficient
mckayFreshUnitExact = Moon.mckay

stageElevenFreshUnitExact :
  J1.FreshUnitExtension.carrierValue J1.stage11FreshUnitExtension
  +
  J1.FreshUnitExtension.freshValue J1.stage11FreshUnitExtension
  ≡
  J1.FreshUnitExtension.joinedValue J1.stage11FreshUnitExtension
stageElevenFreshUnitExact =
  J1.FreshUnitExtension.joinExact J1.stage11FreshUnitExtension

moonshineFreshUnitExact :
  J1.FreshUnitExtension.carrierValue J1.moonshineFreshUnitExtension
  +
  J1.FreshUnitExtension.freshValue J1.moonshineFreshUnitExtension
  ≡
  J1.FreshUnitExtension.joinedValue J1.moonshineFreshUnitExtension
moonshineFreshUnitExact =
  J1.FreshUnitExtension.joinExact J1.moonshineFreshUnitExtension

sharedFreshUnitShapeDoesNotIdentifyValues :
  J1.JPlusOneShapeAnalogy.valuesIdentified J1.canonicalJPlusOneShapeAnalogy
  ≡ false
sharedFreshUnitShapeDoesNotIdentifyValues = refl

sharedFreshUnitShapeDoesNotIdentifySemantics :
  J1.JPlusOneShapeAnalogy.semanticsIdentified J1.canonicalJPlusOneShapeAnalogy
  ≡ false
sharedFreshUnitShapeDoesNotIdentifySemantics = refl

------------------------------------------------------------------------
-- j+1 is successor/rechart semantics in the chart lane.
------------------------------------------------------------------------

chartTenSuccessorIsEleven :
  Chart.nextChart (Chart.chart 10) ≡ Chart.chart 11
chartTenSuccessorIsEleven = refl

residualGluingFailureRechartsToEleven :
  Rechart.chart (Rechart.rechart Rechart.stateAtStar) ≡ Chart.chart 11
residualGluingFailureRechartsToEleven =
  Rechart.starRechartsToEleven

jRoleSeparationRetained :
  Chart.JRoleBoundary.chartAndModularIdentifiedWithoutBridge
    Chart.canonicalJRoleBoundary
  ≡ false
jRoleSeparationRetained = refl

jRepresentationRoleSeparationRetained :
  Chart.JRoleBoundary.chartAndRepresentationIdentifiedWithoutBridge
    Chart.canonicalJRoleBoundary
  ≡ false
jRepresentationRoleSeparationRetained = refl

------------------------------------------------------------------------
-- Carry is a two-depth reading: lower residue remains memory.
------------------------------------------------------------------------

carryRequiresJAndJPlusOneReading :
  Carry.depthEvaluationBoundary Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Carry.evaluateJAndJPlusOneTogether
carryRequiresJAndJPlusOneReading =
  Carry.depthEvaluationBoundaryIsJAndJPlusOne
    Carry.canonicalCarryMemorySubvoxelReceipt

lowerResiduePersistsAcrossCarry :
  Carry.subvoxelMemory Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Carry.lowerResiduePersistsAsMemory
lowerResiduePersistsAcrossCarry =
  Carry.subvoxelMemoryPersists Carry.canonicalCarryMemorySubvoxelReceipt

------------------------------------------------------------------------
-- Tesla and Sweetgrass provenance boundaries stay explicit.
------------------------------------------------------------------------

teslaDoesNotOwnBase369 :
  Tesla.base369AttributedToTesla Tesla.teslaPolyphaseBoundary ≡ false
teslaDoesNotOwnBase369 =
  Tesla.base369-is-modern-extension

teslaUniversal369NotPromoted :
  Tesla.universal369DoctrinePromoted Tesla.teslaPolyphaseBoundary ≡ false
teslaUniversal369NotPromoted =
  Tesla.universal369-is-not-promoted

sweetgrassBraidMotifIsFabricRole :
  Sweetgrass.motifPrimaryRole Sweetgrass.motifSweetgrassBraidFabric
  ≡ Sweetgrass.fabricRole
sweetgrassBraidMotifIsFabricRole = refl

monsterMotifIsMoonshineRole :
  Sweetgrass.motifPrimaryRole Sweetgrass.motifMonsterMoonshine
  ≡ Sweetgrass.moonshineGroupRole
monsterMotifIsMoonshineRole = refl

------------------------------------------------------------------------
-- A compact typed picture of the broader math spine.
------------------------------------------------------------------------

data CrossScaleOperation : Set where
  addressWithinChart : CrossScaleOperation
  retainResidual : CrossScaleOperation
  rechartAtJPlusOne : CrossScaleOperation
  reopenFromResidual : CrossScaleOperation
  weaveIntoFabric : CrossScaleOperation
  extendByFreshUnit : CrossScaleOperation
  refineSixToNine : CrossScaleOperation
  forgetNineToThree : CrossScaleOperation

data CrossScaleInvariant : Set where
  lowerHistoryRetained : CrossScaleInvariant
  provenanceRetained : CrossScaleInvariant
  carrierIdentityNotInferred : CrossScaleInvariant
  semanticAuthorityNotInferred : CrossScaleInvariant
  forgetfulDirectionRemembered : CrossScaleInvariant

record JPlusOne369FibreCarryBoundary : Set where
  constructor jPlusOne369FibreCarryBoundary
  field
    twentySevenIsAddressGeometry : Bool
    twentySevenExhaustsSemanticStates : Bool
    residualCanSeedRechart : Bool
    rechartErasesLowerHistory : Bool
    jAndJPlusOneShouldBeReadTogetherForCarry : Bool
    sixEmbedsInNinePreservingDepthPhase : Bool
    nineRetractsToSixWithoutZeroPolicy : Bool
    McKayAndChartJAreSameCarrier : Bool
    TeslaHistoricallyOwnsDASHI369 : Bool
    fabricVocabularyImpliesDomainIdentity : Bool

canonicalJPlusOne369FibreCarryBoundary :
  JPlusOne369FibreCarryBoundary
canonicalJPlusOne369FibreCarryBoundary =
  jPlusOne369FibreCarryBoundary
    true false true false true true false false false false
