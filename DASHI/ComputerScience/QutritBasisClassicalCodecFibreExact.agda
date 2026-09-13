module DASHI.ComputerScience.QutritBasisClassicalCodecFibreExact where

open import DASHI.Core.Prelude
open import Data.Maybe using (Maybe; just; nothing)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.InvolutiveTernaryExistingSpineBridge as Involutive
import DASHI.Codec.VerifiedFiniteTritCoder as TwoBit
import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as BinaryInTernary
import DASHI.ComputerScience.BalancedTernaryQutritBasisBridgeExact as QutritBridge
import DASHI.ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact as Dihedral
import DASHI.Algebra.Quantum.FiniteQutrit as Qutrit
import DASHI.Algebra.Quantum.QutritWeyl as Weyl

------------------------------------------------------------------------
-- QUTRIT COMPUTATIONAL BASIS <-> EXISTING CLASSICAL CODEC FIBRES
--
-- The qutrit basis is first converted to the canonical SSP balanced-trit label.
-- That label can then use the already-owned two-bit trit coder.  This is an
-- exact basis-label codec only; a general quantum qutrit state/superposition is
-- not represented by these two bits.
------------------------------------------------------------------------

qutritBasisToTwoBit : Qutrit.QutritBasis → TwoBit.Word2
qutritBasisToTwoBit q =
  TwoBit.encodeTrit (SSP.toTrit (QutritBridge.qutritBasisToTrit q))

twoBitToQutritBasis : TwoBit.Word2 → Maybe Qutrit.QutritBasis
twoBitToQutritBasis TwoBit.word00 = just Qutrit.ket2
twoBitToQutritBasis TwoBit.word01 = just Qutrit.ket0
twoBitToQutritBasis TwoBit.word10 = just Qutrit.ket1
twoBitToQutritBasis TwoBit.word11 = nothing

qutritTwoBitRoundTrip :
  (q : Qutrit.QutritBasis) →
  twoBitToQutritBasis (qutritBasisToTwoBit q) ≡ just q
qutritTwoBitRoundTrip Qutrit.ket0 = refl
qutritTwoBitRoundTrip Qutrit.ket1 = refl
qutritTwoBitRoundTrip Qutrit.ket2 = refl

reservedTwoBitWordRejected :
  twoBitToQutritBasis TwoBit.word11 ≡ nothing
reservedTwoBitWordRejected = refl

------------------------------------------------------------------------
-- Binary data can also enter the qutrit basis through the existing strict
-- nonzero balanced-ternary subcarrier.  The centre/ket0 is unused by this Bool
-- embedding, exactly mirroring the ternary subcarrier theorem.
------------------------------------------------------------------------

bitToQutritBasis : Bool → Qutrit.QutritBasis
bitToQutritBasis b =
  QutritBridge.tritToQutritBasis (BinaryInTernary.embedBit b)

qutritBasisToEmbeddedBit : Qutrit.QutritBasis → Bool
qutritBasisToEmbeddedBit q =
  BinaryInTernary.decodeEmbeddedBit (QutritBridge.qutritBasisToTrit q)

bitQutritRoundTrip :
  (b : Bool) → qutritBasisToEmbeddedBit (bitToQutritBasis b) ≡ b
bitQutritRoundTrip false = refl
bitQutritRoundTrip true = refl

bitImageAvoidsKet0 :
  (b : Bool) → bitToQutritBasis b ≡ Qutrit.ket0 → ⊥
bitImageAvoidsKet0 false ()
bitImageAvoidsKet0 true ()

------------------------------------------------------------------------
-- Transport the C2 antipode to the qutrit computational basis.  It swaps
-- ket1/ket2 and fixes ket0; this is distinct from the Weyl C3 shift X.
------------------------------------------------------------------------

qutritBasisAntipode : Qutrit.QutritBasis → Qutrit.QutritBasis
qutritBasisAntipode q =
  QutritBridge.tritToQutritBasis
    (Involutive.sspι (QutritBridge.qutritBasisToTrit q))

qutritBasisAntipodeKet0 : qutritBasisAntipode Qutrit.ket0 ≡ Qutrit.ket0
qutritBasisAntipodeKet0 = refl

qutritBasisAntipodeKet1 : qutritBasisAntipode Qutrit.ket1 ≡ Qutrit.ket2
qutritBasisAntipodeKet1 = refl

qutritBasisAntipodeKet2 : qutritBasisAntipode Qutrit.ket2 ≡ Qutrit.ket1
qutritBasisAntipodeKet2 = refl

qutritBasisAntipodeInvolutive :
  (q : Qutrit.QutritBasis) →
  qutritBasisAntipode (qutritBasisAntipode q) ≡ q
qutritBasisAntipodeInvolutive Qutrit.ket0 = refl
qutritBasisAntipodeInvolutive Qutrit.ket1 = refl
qutritBasisAntipodeInvolutive Qutrit.ket2 = refl

qutritDihedralRelation :
  (q : Qutrit.QutritBasis) →
  qutritBasisAntipode (Weyl.X (qutritBasisAntipode q))
  ≡ Weyl.X (Weyl.X q)
qutritDihedralRelation Qutrit.ket0 = refl
qutritDihedralRelation Qutrit.ket1 = refl
qutritDihedralRelation Qutrit.ket2 = refl

record QutritBasisClassicalCodecBoundary : Set where
  constructor qutritBasisClassicalCodecBoundary
  field
    qutritBasisTwoBitRoundTrips : Bool
    malformedTwoBitWordRejected : Bool
    boolEmbedsViaExistingTernarySubcarrier : Bool
    boolEmbeddingUsesKet0 : Bool
    c2AntipodeTransportedToBasis : Bool
    c3WeylShiftRemainsDistinct : Bool
    dihedralRelationExactOnBasis : Bool
    twoBitsEncodeGeneralQutritSuperposition : Bool
    binaryAndTernaryCarriersIdentified : Bool

canonicalQutritBasisClassicalCodecBoundary :
  QutritBasisClassicalCodecBoundary
canonicalQutritBasisClassicalCodecBoundary =
  qutritBasisClassicalCodecBoundary
    true true true false true true true false false
