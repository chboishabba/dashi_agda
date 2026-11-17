module DASHI.Analysis.PickoverSignedSSPTorquePhaseBridgeExact where

------------------------------------------------------------------------
-- PICKOVER 99 / SIGNED SSP / TORQUE-C3 SAME-OBSERVER MAX-CUT
--
-- Attribution:
-- John Conway: FRACTRAN and ordered positive-integer fractions.
-- Classical: integer valuations, Euler/CRT and U(1) oriented area.
-- Existing DASHI:
--  Biology.SignedSSPFRACTRANWeaveExact (fifteen-lane signed state);
--  Physics.Foundations.OrientedThreeAxisBracket369Exact (torque phase);
--  Moonshine.JInvariant369SignedSSPFRACTRANPhaseFibreExact (signed
--    spectral conjugation already paid);
--  Analysis.RiemannSSP15ProducerMarkedSignedFRACTRANExact (conditional
--    RH O/j/s producer roles, not analytic sine signs).
--
-- This module specialises/joins existing owners.  The chosen mapping from
-- a signed arithmetic orientation to an oriented torque voxel is an
-- orientation CODEC, not a physical mechanism identification.
-- No Hardy zero, RH, or sine(99^(9999!)) sign is manufactured.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Torque
import DASHI.Moonshine.C3FourierConjugationExact as C3
import DASHI.Algebra.TriadicDepthOneCharacters as C3Base
import DASHI.Foundations.Base369Nat as Mod
import DASHI.Mathematics.NumberTheory.EisensteinNineCRTPhaseMaxCutExact as CRT

------------------------------------------------------------------------
-- The existing SSP coarse observer and the torque bracket use different
-- trit datatypes.  This explicit three-case map pays that exact type seam.
------------------------------------------------------------------------

kernelToTorqueTrit : Triadic.KernelTrit → BT.Trit
kernelToTorqueTrit Triadic.negativeTrit = BT.neg
kernelToTorqueTrit Triadic.zeroTrit = BT.zero
kernelToTorqueTrit Triadic.positiveTrit = BT.pos

orientationToTorqueTrit : SSP.FibreOrientation → BT.Trit
orientationToTorqueTrit SSP.inverseOrientation = BT.neg
orientationToTorqueTrit SSP.mediatedOrientation = BT.zero
orientationToTorqueTrit SSP.forwardOrientation = BT.pos

torqueVoxelFromOrientation :
  SSP.FibreOrientation → Torque.BracketVoxel
torqueVoxelFromOrientation SSP.inverseOrientation = Torque.xzyBracket
torqueVoxelFromOrientation SSP.mediatedOrientation = Torque.xxyBracket
torqueVoxelFromOrientation SSP.forwardOrientation = Torque.xyzBracket

torqueVoxelFromSigned :
  SSP.SignedMultiplicity → Torque.BracketVoxel
torqueVoxelFromSigned m =
  torqueVoxelFromOrientation (SSP.orientationOfMultiplicity m)

signedCoarseEqualsTorqueOrientation :
  (m : SSP.SignedMultiplicity) →
  kernelToTorqueTrit (SSP.coarseMultiplicity m)
  ≡ Torque.bracketOrientation (torqueVoxelFromSigned m)
signedCoarseEqualsTorqueOrientation (SSP.negativeMultiplicity n) = refl
signedCoarseEqualsTorqueOrientation SSP.zeroMultiplicity = refl
signedCoarseEqualsTorqueOrientation (SSP.positiveMultiplicity n) = refl

signedNegationNegatesTorqueOrientation :
  (m : SSP.SignedMultiplicity) →
  Torque.bracketOrientation
    (torqueVoxelFromSigned (SSP.negateMultiplicity m))
  ≡ BT.negate (Torque.bracketOrientation (torqueVoxelFromSigned m))
signedNegationNegatesTorqueOrientation
  (SSP.negativeMultiplicity n) = refl
signedNegationNegatesTorqueOrientation SSP.zeroMultiplicity = refl
signedNegationNegatesTorqueOrientation
  (SSP.positiveMultiplicity n) = refl

signedNegationConjugatesTorquePhase :
  (m : SSP.SignedMultiplicity) →
  Torque.bracketPhase
    (torqueVoxelFromSigned (SSP.negateMultiplicity m))
  ≡ C3.inversePhase (Torque.bracketPhase (torqueVoxelFromSigned m))
signedNegationConjugatesTorquePhase
  (SSP.negativeMultiplicity n) = refl
signedNegationConjugatesTorquePhase SSP.zeroMultiplicity = refl
signedNegationConjugatesTorquePhase
  (SSP.positiveMultiplicity n) = refl

signedNegationMatchesTorqueInputReversalAtPhase :
  (m : SSP.SignedMultiplicity) →
  Torque.bracketPhase
    (Torque.swapBracketInputs (torqueVoxelFromSigned m))
  ≡ Torque.bracketPhase
    (torqueVoxelFromSigned (SSP.negateMultiplicity m))
signedNegationMatchesTorqueInputReversalAtPhase m =
  trans
    (Torque.swapBracketInputsConjugatesPhase (torqueVoxelFromSigned m))
    (sym (signedNegationConjugatesTorquePhase m))

-- The chart maps inverse/mediated/forward to the existing exact ordered
-- torque phases zeta^2 / 1 / zeta, including a genuine neutral sector.

inverseSSPPhaseIsZetaSquared :
  Torque.bracketPhase
    (torqueVoxelFromOrientation SSP.inverseOrientation)
  ≡ C3.zetaSquared
inverseSSPPhaseIsZetaSquared = refl

neutralSSPPhaseIsOne :
  Torque.bracketPhase
    (torqueVoxelFromOrientation SSP.mediatedOrientation)
  ≡ C3.one
neutralSSPPhaseIsOne = refl

forwardSSPPhaseIsZeta :
  Torque.bracketPhase
    (torqueVoxelFromOrientation SSP.forwardOrientation)
  ≡ C3.zeta
forwardSSPPhaseIsZeta = refl

------------------------------------------------------------------------
-- The 99/1 FRACTRAN step has prime-exponent delta (v3,v11)=(2,1).
-- Do NOT create a 99-prime lane or a 101-prime lane in SSP15: 99 is
-- composite and 101 is an EXTERNAL CRT component, not an Ogg prime.
--
-- This is a symbolic valuation of the integer 99^k, NOT a proof that
-- the WeaveEffect counter is the literal integer FRACTRAN machine.
------------------------------------------------------------------------

positiveAt : Nat → SSP.SignedMultiplicity
positiveAt zero = SSP.zeroMultiplicity
positiveAt (suc n) = SSP.positiveMultiplicity (suc n)

signed99PowerValuation : Nat → SSP.SSPValuation
signed99PowerValuation k SSP.ssp3 = positiveAt (k + k)
signed99PowerValuation k SSP.ssp11 = positiveAt k
signed99PowerValuation k prime = SSP.zeroMultiplicity

zeroPowerHasZeroAtThree :
  signed99PowerValuation 0 SSP.ssp3 ≡ SSP.zeroMultiplicity
zeroPowerHasZeroAtThree = refl

zeroPowerHasZeroAtEleven :
  signed99PowerValuation 0 SSP.ssp11 ≡ SSP.zeroMultiplicity
zeroPowerHasZeroAtEleven = refl

onePowerHasTwoThreeTokens :
  signed99PowerValuation 1 SSP.ssp3 ≡ SSP.positiveMultiplicity 2
onePowerHasTwoThreeTokens = refl

onePowerHasOneElevenToken :
  signed99PowerValuation 1 SSP.ssp11 ≡ SSP.positiveMultiplicity 1
onePowerHasOneElevenToken = refl

sixPowerHasTwelveThreeTokens :
  signed99PowerValuation 6 SSP.ssp3 ≡ SSP.positiveMultiplicity 12
sixPowerHasTwelveThreeTokens = refl

sixPowerHasSixElevenTokens :
  signed99PowerValuation 6 SSP.ssp11 ≡ SSP.positiveMultiplicity 6
sixPowerHasSixElevenTokens = refl

oneAndSixHaveSameCoarseThreePolarity :
  SSP.coarseMultiplicity (signed99PowerValuation 1 SSP.ssp3)
  ≡ SSP.coarseMultiplicity (signed99PowerValuation 6 SSP.ssp3)
oneAndSixHaveSameCoarseThreePolarity = refl

oneAndSixHaveSameCoarseElevenPolarity :
  SSP.coarseMultiplicity (signed99PowerValuation 1 SSP.ssp11)
  ≡ SSP.coarseMultiplicity (signed99PowerValuation 6 SSP.ssp11)
oneAndSixHaveSameCoarseElevenPolarity = refl

-- The actual existing WEAVE instruction language retains the two named
-- prime lanes, unlike its aggregate WeaveEffect token-count observation.
-- It is an instruction-level *presentation* of delta (2,1), not a claim
-- that this program literally executes FRACTRAN arithmetic on integers.

signed99PrimeInstructionWord : List SSP.WeaveInstruction
signed99PrimeInstructionWord =
  SSP.introducePrime SSP.ssp3
  ∷ SSP.introducePrime SSP.ssp3
  ∷ SSP.introducePrime SSP.ssp11
  ∷ []

threeInstructionsEncodeTwoAndOne :
  SSP.positivePrimeTokens
    (SSP.executeProgram signed99PrimeInstructionWord SSP.emptyWeaveEffect)
  ≡ 3
threeInstructionsEncodeTwoAndOne = refl

------------------------------------------------------------------------
-- The finite torsion C101 consumer is EXACTLY where the 9999! power map
-- becomes a projector: k -> 4950*k mod 9999 = 99*(50*k mod 101).
-- The two formulae are checked by exact small representatives and an
-- exhaustive integer regression.  No e^i -> torsion approximation is given.
------------------------------------------------------------------------

torsionProjector : Nat → Nat
torsionProjector k = Mod._%_ (4950 * k) 9999

torsionImage101Coordinate : Nat → Nat
torsionImage101Coordinate k = Mod._%_ (50 * k) 101

projectorAtOne :
  torsionProjector 1 ≡ 4950
projectorAtOne = refl

torsionImageAtOne :
  torsionImage101Coordinate 1 ≡ 50
torsionImageAtOne = refl

torsionImageAtNinetyNine :
  torsionImage101Coordinate 99 ≡ 1
torsionImageAtNinetyNine = refl

projectorKillsOneOhOne :
  torsionProjector 101 ≡ 0
projectorKillsOneOhOne = refl

projectorPreservesOneOhOneGenerator :
  torsionProjector 99 ≡ 99
projectorPreservesOneOhOneGenerator = refl

-- No false identification of three fundamentally different consumers.
record AnalyticBoundary : Set where
  constructor analytic-boundary
  field
    finiteSSPTorquePhaseIntertwinerPresent : Bool
    composite99FactorVectorPresent : Bool
    torsion101ProjectorPresent : Bool
    actualCirclePhaseAttachmentPresent : Bool
    rHActualZetaSignedEstimatePresent : Bool
    pickover9999SineSignCertified : Bool

canonicalAnalyticBoundary : AnalyticBoundary
canonicalAnalyticBoundary =
  analytic-boundary true true true false false false
