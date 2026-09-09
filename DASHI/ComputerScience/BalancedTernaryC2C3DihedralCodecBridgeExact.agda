module DASHI.ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.InvolutiveTernaryExistingSpineBridge as Involutive
import DASHI.Codec.BalancedTritBitFibre as BitFibre
import DASHI.ComputerScience.BalancedTernaryQutritBasisBridgeExact as QutritBridge
import DASHI.Algebra.Quantum.QutritWeyl as Weyl

------------------------------------------------------------------------
-- ONE THREE-STATE CARRIER, TWO DISTINCT ACTIONS
--
-- The established SSP carrier supports:
--   * a C2 antipode/involution, transported exactly through the support/sign
--     binary fibre; and
--   * a C3 cyclic successor, transported exactly to the qutrit Weyl X basis
--     shift.
--
-- These are not the same operation.  Together they satisfy the standard
-- dihedral relation i c i = c^-1 = c^2 on a three-point carrier.
------------------------------------------------------------------------

antipode : SSP.SSPTrit → SSP.SSPTrit
antipode = Involutive.sspι

cycle : SSP.SSPTrit → SSP.SSPTrit
cycle = QutritBridge.cycleC3

cycleInverse : SSP.SSPTrit → SSP.SSPTrit
cycleInverse t = cycle (cycle t)

antipodeOrderTwo : (t : SSP.SSPTrit) → antipode (antipode t) ≡ t
antipodeOrderTwo = Involutive.sspι-involutive

cycleOrderThree :
  (t : SSP.SSPTrit) → cycle (cycle (cycle t)) ≡ t
cycleOrderThree = QutritBridge.cycleC3OrderThree

antipodeConjugatesCycleToInverse :
  (t : SSP.SSPTrit) →
  antipode (cycle (antipode t)) ≡ cycleInverse t
antipodeConjugatesCycleToInverse SSP.sspNegOne = refl
antipodeConjugatesCycleToInverse SSP.sspZero = refl
antipodeConjugatesCycleToInverse SSP.sspPosOne = refl

------------------------------------------------------------------------
-- C2 presentation: exact support/sign binary fibre.
------------------------------------------------------------------------

binaryPresentation : SSP.SSPTrit → BitFibre.TritFibre
binaryPresentation t = BitFibre.encodeFibre (SSP.toTrit t)

binaryDecode : BitFibre.TritFibre → SSP.SSPTrit
binaryDecode f = SSP.fromTrit (BitFibre.decodeFibre f)

binaryDecodeEncode :
  (t : SSP.SSPTrit) → binaryDecode (binaryPresentation t) ≡ t
binaryDecodeEncode SSP.sspNegOne = refl
binaryDecodeEncode SSP.sspZero = refl
binaryDecodeEncode SSP.sspPosOne = refl

binaryEncodeDecode :
  (f : BitFibre.TritFibre) → binaryPresentation (binaryDecode f) ≡ f
binaryEncodeDecode BitFibre.zeroFibre = refl
binaryEncodeDecode (BitFibre.signedFibre BitFibre.positiveSign) = refl
binaryEncodeDecode (BitFibre.signedFibre BitFibre.negativeSign) = refl

binaryPresentationIntertwinesAntipode :
  (t : SSP.SSPTrit) →
  binaryPresentation (antipode t)
  ≡ BitFibre.invertFibre (binaryPresentation t)
binaryPresentationIntertwinesAntipode SSP.sspNegOne = refl
binaryPresentationIntertwinesAntipode SSP.sspZero = refl
binaryPresentationIntertwinesAntipode SSP.sspPosOne = refl

binarySupportForgetsOnlyOrientation :
  (t : SSP.SSPTrit) →
  BitFibre.supportBit (binaryPresentation (antipode t))
  ≡ BitFibre.supportBit (binaryPresentation t)
binarySupportForgetsOnlyOrientation SSP.sspNegOne = refl
binarySupportForgetsOnlyOrientation SSP.sspZero = refl
binarySupportForgetsOnlyOrientation SSP.sspPosOne = refl

------------------------------------------------------------------------
-- C3 presentation: exact qutrit computational-basis chart.
------------------------------------------------------------------------

qutritPresentationIntertwinesCycle :
  (t : SSP.SSPTrit) →
  QutritBridge.tritToQutritBasis (cycle t)
  ≡ Weyl.X (QutritBridge.tritToQutritBasis t)
qutritPresentationIntertwinesCycle = QutritBridge.weylXIntertwinesC3Cycle

------------------------------------------------------------------------
-- The same dihedral relation survives after translating the endpoints through
-- either exact presentation.  We do not claim a support/sign fibre is a qutrit
-- state, or that a qutrit superposition is classical ternary storage.
------------------------------------------------------------------------

qutritDihedralEndpoint :
  (t : SSP.SSPTrit) →
  QutritBridge.tritToQutritBasis (antipode (cycle (antipode t)))
  ≡ QutritBridge.tritToQutritBasis (cycleInverse t)
qutritDihedralEndpoint t = cong QutritBridge.tritToQutritBasis
  (antipodeConjugatesCycleToInverse t)

record BalancedTernaryC2C3DihedralBoundary : Set where
  constructor balancedTernaryC2C3DihedralBoundary
  field
    c2AntipodeExact : Bool
    c3CycleExact : Bool
    dihedralCompatibilityExact : Bool
    binarySupportSignIntertwinesC2 : Bool
    qutritBasisIntertwinesC3 : Bool
    antipodeEqualsCycle : Bool
    binaryFibreEqualsQuantumQutritState : Bool
    qutritBasisChartIncludesGeneralSuperpositions : Bool

canonicalBalancedTernaryC2C3DihedralBoundary :
  BalancedTernaryC2C3DihedralBoundary
canonicalBalancedTernaryC2C3DihedralBoundary =
  balancedTernaryC2C3DihedralBoundary
    true true true true true false false false
