module DASHI.Physics.Gravity.KKE6Full27CSMassSignConsumerExact where

------------------------------------------------------------------------
-- Selected 5D parity-odd full27 source: mass SIGN chambers.
-- Original group branching from Slansky E6 -> SU3c x SU3L x SU3R:
-- 27 = (3,bar3,1)+(bar3,1,3)+(1,3,bar3).
-- A 5D Dirac loop supplies source-dependent parity odd half-shifts:
-- k_c = 3/2 (sA-sB); k_L = 3/2 (sC-sA);
-- k_R = 3/2 (sB-sC), in a chosen LOCAL cubic-index convention.
-- Relative signs ±1 make these 0,+3,-3; a COMMON sign makes 0.
--
-- This exact finite classification is NOT a 5D spin-CS functional,
-- global SU3^3 quotient/large-gauge proof, or APS eta calculation.
-- Earlier QFT CSLevelFlowFullReceipt is 2+1D conditional CS;
-- original Bonetti-Grimm-Hohenegger 2013 owns induced 5D CS theory.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Physics.QFT.FermionicLoopCSShiftReceipt as SourceCS

data FiveDMassSign : Set where
  positiveMass negativeMass : FiveDMassSign

data LocalPureSUThreeShift : Set where
  minusThree zeroShift plusThree : LocalPureSUThreeShift

relativeMassSignCSShift :
  FiveDMassSign → FiveDMassSign → LocalPureSUThreeShift
relativeMassSignCSShift positiveMass positiveMass = zeroShift
relativeMassSignCSShift negativeMass negativeMass = zeroShift
relativeMassSignCSShift positiveMass negativeMass = plusThree
relativeMassSignCSShift negativeMass positiveMass = minusThree

record Trinification27MassChamber : Set where
  constructor mk27MassChamber
  field
    massA massB massC : FiveDMassSign
open Trinification27MassChamber public

full27UniformPositive : Trinification27MassChamber
full27UniformPositive =
  mk27MassChamber positiveMass positiveMass positiveMass

full27UniformNegative : Trinification27MassChamber
full27UniformNegative =
  mk27MassChamber negativeMass negativeMass negativeMass

full27SplitAplusBminusCplus : Trinification27MassChamber
full27SplitAplusBminusCplus =
  mk27MassChamber positiveMass negativeMass positiveMass

inducedPureColourShift : Trinification27MassChamber →
  LocalPureSUThreeShift
inducedPureColourShift s =
  relativeMassSignCSShift (massA s) (massB s)

inducedPureLeftShift : Trinification27MassChamber →
  LocalPureSUThreeShift
inducedPureLeftShift s =
  relativeMassSignCSShift (massC s) (massA s)

inducedPureRightShift : Trinification27MassChamber →
  LocalPureSUThreeShift
inducedPureRightShift s =
  relativeMassSignCSShift (massB s) (massC s)

positive27PureCSZero :
  inducedPureColourShift full27UniformPositive ≡ zeroShift
positive27PureCSZero = refl

negative27PureCSZero :
  inducedPureColourShift full27UniformNegative ≡ zeroShift
negative27PureCSZero = refl

split27ColourCSPlusThree :
  inducedPureColourShift full27SplitAplusBminusCplus ≡ plusThree
split27ColourCSPlusThree = refl

split27LeftCSZero :
  inducedPureLeftShift full27SplitAplusBminusCplus ≡ zeroShift
split27LeftCSZero = refl

split27RightCSMinusThree :
  inducedPureRightShift full27SplitAplusBminusCplus ≡ minusThree
split27RightCSMinusThree = refl

zeroNotPlusThree : zeroShift ≡ plusThree → ⊥
zeroNotPlusThree ()

-- The same SU3^3 representation carrier has identical 27-dimensional
-- cardinality and cubic INDEX for all sign configurations, but its
-- regulator-dependent induced CS shifts are not the same.
constantRepresentationCount : Trinification27MassChamber → Nat
constantRepresentationCount _ = 27

full27RepresentationDoesNotDetermineInducedCS :
  Transport.ClaimNonTransportWitness
    constantRepresentationCount inducedPureColourShift
full27RepresentationDoesNotDetermineInducedCS =
  Descent.consumerNonDescentWitness
    full27UniformPositive full27SplitAplusBminusCplus
    refl zeroNotPlusThree

noFull27CubicIndexPromotionToFiveDCS :
  Transport.ClaimTransport
    constantRepresentationCount inducedPureColourShift → ⊥
noFull27CubicIndexPromotionToFiveDCS =
  Transport.claimNonTransportWitnessBlocksTransport
    full27RepresentationDoesNotDetermineInducedCS

-- The source's finite lower-dimensional fermionic CS-level receipt
-- remains a separate ORIGINAL donor, not a 5D mass-sign derivation.
olderConditionalCSOwner : SourceCS.FermionicLoopCSShiftReceipt
olderConditionalCSOwner =
  SourceCS.canonicalFermionicLoopCSShiftReceipt
