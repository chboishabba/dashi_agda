module DASHI.Physics.Gravity.KKE6TrinificationSourceConsumerBIDIExact where

------------------------------------------------------------------------
-- LITERAL CROSS-PR SOURCE OWNERS (DO NOT INVENT NEW PHYSICAL THEORY)
-- PR #1106 Ternary27TrinificationE6SameActionExact:
--    27 first-Tits, same cubic SL3^3 action; two E32/E33 Higgs 27s.
-- PR #1106 Ternary27TrinificationTwoVEVGeneralMassSpectrumExact:
--    4 zero 5D vector modes, 12 broken ones at positive couplings.
-- PR #1106 Ternary27TrinificationTwoVEVLocalStabilityExact:
--    36 real Higgs coordinates, 12 eaten Goldstones, 24 physical.
-- PR #1164 ContinuousSO3Torque369BridgeExact: spatial SO3 torque,
--    NOT a nontrivial SO3 -> KK-fibre U1 Lie-algebra homomorphism.
-- PR #1235 HopfU1 bundle source: local gauge fibre/cocycle obligations.
--
-- The sibling source claims are NOT imported as Agda proofs in this
-- unmerged PR; below are exact selected dimension/consumer arithmetic.
-- Action / gauge fixing / quantum determinant / source metric variation
-- / chiral electroweak data remain source-side physical obligations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_*_; _∸_)

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

originalLRGaugeGenerators : Nat
originalLRGaugeGenerators = 2 * 8

unbrokenLRYGaugeGenerators : Nat
unbrokenLRYGaugeGenerators = 4

brokenLRGaugeGenerators : Nat
brokenLRGaugeGenerators = 12

twoBifundamentalRealScalarCoordinates : Nat
twoBifundamentalRealScalarCoordinates = 2 * 2 * 3 * 3

eatenGaugeOrbitGoldstones : Nat
eatenGaugeOrbitGoldstones = 12

uneatenPhysicalHiggsCoordinates : Nat
uneatenPhysicalHiggsCoordinates =
  twoBifundamentalRealScalarCoordinates ∸ eatenGaugeOrbitGoldstones

correctGaugeRank : unbrokenLRYGaugeGenerators + brokenLRGaugeGenerators ≡ 16
correctGaugeRank = refl

correctPhysicalHiggsCount : uneatenPhysicalHiggsCoordinates ≡ 24
correctPhysicalHiggsCount = refl

unbrokenFiveDimensionalVectorPolarizations : Nat
unbrokenFiveDimensionalVectorPolarizations =
  unbrokenLRYGaugeGenerators * 3

massiveFiveDimensionalVectorPolarizations : Nat
massiveFiveDimensionalVectorPolarizations =
  brokenLRGaugeGenerators * 4

beforeBreakingFullBosonCount : Nat
beforeBreakingFullBosonCount =
  originalLRGaugeGenerators * 3
  + twoBifundamentalRealScalarCoordinates

afterBreakingFullBosonCount : Nat
afterBreakingFullBosonCount =
  unbrokenFiveDimensionalVectorPolarizations
  + massiveFiveDimensionalVectorPolarizations
  + uneatenPhysicalHiggsCoordinates

beforeCountIsEightyFour : beforeBreakingFullBosonCount ≡ 84
beforeCountIsEightyFour = refl

afterCountIsEightyFour : afterBreakingFullBosonCount ≡ 84
afterCountIsEightyFour = refl

-- NOT the same consumer as two unbroken SU3 octets: 16*3=48.
masslessOctetOnlyCount : 2 * 8 * 3 ≡ 48
masslessOctetOnlyCount = refl

-- A massless fifth-dimensional spin-one has 3, a massive Proca has 4.
massiveVectorCountsCannotReuseMasslessThreePol : 12 * 4 ≡ 48
massiveVectorCountsCannotReuseMasslessThreePol = refl

-- Separate physical gauge candidate labels: SAME inherited E6 four
-- unbroken generators, different photon identifications.
data PhysicalPhotonSourceChoice : Set where
  retainExtraIndependentMaxwell
    identifySourceBeforeCompactification : PhysicalPhotonSourceChoice

sameE6NeutralGaugeRank : PhysicalPhotonSourceChoice → Nat
sameE6NeutralGaugeRank retainExtraIndependentMaxwell = 4
sameE6NeutralGaugeRank identifySourceBeforeCompactification = 4

data ObservableUnbrokenPhotonCount : Set where
  twoIndependentPhotons onePhysicalPhoton : ObservableUnbrokenPhotonCount

photonReadout : PhysicalPhotonSourceChoice → ObservableUnbrokenPhotonCount
photonReadout retainExtraIndependentMaxwell = twoIndependentPhotons
photonReadout identifySourceBeforeCompactification = onePhysicalPhoton

distinctPhotonCount : twoIndependentPhotons ≡ onePhysicalPhoton → ⊥
distinctPhotonCount ()

sameE6RankCannotDeterminePhotonIdentification :
  Transport.ClaimNonTransportWitness sameE6NeutralGaugeRank photonReadout
sameE6RankCannotDeterminePhotonIdentification =
  Descent.consumerNonDescentWitness
    retainExtraIndependentMaxwell
    identifySourceBeforeCompactification
    refl distinctPhotonCount

photonConsumerRequiresActualSourceIdentification :
  Transport.ClaimTransport sameE6NeutralGaugeRank photonReadout → ⊥
photonConsumerRequiresActualSourceIdentification =
  Transport.claimNonTransportWitnessBlocksTransport
    sameE6RankCannotDeterminePhotonIdentification

-- Small elementary parity/CS charge-lattice counts for the eight
-- elected SU3-fundamental Dirac modes in unit q3=3 Qem convention.
-- Charge moments are NECESSARY regulator bookkeeping, not
-- sufficient mixed SU3-U1/Z3-spin/global parity anomaly authority.
eightFundamentalCount : 6 + 2 ≡ 8
eightFundamentalCount = refl

electricChargeSumInThirds : 4 * 2 ≡ 4 + 4 * 1
electricChargeSumInThirds = refl

halfLevelSUThreeCandidateIntegral : 8 ≡ 2 * 4
halfLevelSUThreeCandidateIntegral = refl

-- Distinct spatial SO3 torque and fibre U1 have no promoted physical
-- action identification merely from hypervoxel orientation.
data PhysicalOperatorKind : Set where
  spatialSOThreeTorque geometricCircleUOneShift : PhysicalOperatorKind

operatorLabel : PhysicalOperatorKind → Nat
operatorLabel spatialSOThreeTorque = 369
operatorLabel geometricCircleUOneShift = 369

physicalOperatorConsumer : PhysicalOperatorKind → PhysicalOperatorKind
physicalOperatorConsumer x = x

differentOperators : spatialSOThreeTorque ≡ geometricCircleUOneShift → ⊥
differentOperators ()

orientationLabelDoesNotDetermineCompactFibreAction :
  Transport.ClaimNonTransportWitness operatorLabel physicalOperatorConsumer
orientationLabelDoesNotDetermineCompactFibreAction =
  Descent.consumerNonDescentWitness
    spatialSOThreeTorque geometricCircleUOneShift refl differentOperators


------------------------------------------------------------------------
-- Do NOT conflate selected 3×3 bifundamental scalar components with
-- TWO full complex E6 27-plet scalar multiplets, or with full gauged E6.
-- Original E6 650 Higgs source is independent published model building,
-- not an inhabitant derived from the first-Tits source owner.
------------------------------------------------------------------------

twoFullComplexTwentySevensRealCount : 2 * 27 * 2 ≡ 108
twoFullComplexTwentySevensRealCount = refl

suThreeCubedTwoSelectedBifundamentalsTotal :
  24 * 3 + 36 ≡ 8 * 3 + 4 * 3 + 12 * 4 + 24
suThreeCubedTwoSelectedBifundamentalsTotal = refl

suThreeCubedTwoFullComplexTwentySevensTotal :
  24 * 3 + 108 ≡ 8 * 3 + 4 * 3 + 12 * 4 + 96
suThreeCubedTwoFullComplexTwentySevensTotal = refl

eSixToTrinificationBrokenGeneratorCount :
  78 ∸ 24 ≡ 54
eSixToTrinificationBrokenGeneratorCount = refl

eSixToSMBrokenGeneratorCount :
  78 ∸ 12 ≡ 66
eSixToSMBrokenGeneratorCount = refl

fullESixPublished650PlusTwo27PhysicalBosonCount :
  78 * 3 + 650 + 108
    ≡ 12 * 3 + 66 * 4 + ((650 + 108) ∸ 66)
fullESixPublished650PlusTwo27PhysicalBosonCount = refl

-- Different source spectra can share algebraic rank/27-labels.
-- Neither reuses a selected 36-coordinate mass Hessian for 108 or 758
-- coordinates without an explicit action and same-spectrum receipt.
