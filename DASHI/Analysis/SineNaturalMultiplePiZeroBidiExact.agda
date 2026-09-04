module DASHI.Analysis.SineNaturalMultiplePiZeroBidiExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

import DASHI.Analysis.ConstructiveRealSpine as R
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Analysis.OrdinaryTranscendentalRealization as Trig
import DASHI.Analysis.SineZeroClassificationSourceAuthorityExact as Source

------------------------------------------------------------------------
-- BIDI SINE-ZERO SPLIT
--
-- Forward direction is internal and exact:
--
--   n : Nat  ->  sin (n*pi) = 0.
--
-- Reverse direction remains separate:
--
--   sin x = 0  ->  exists integer n, x = n*pi.
--
-- The reverse classification is source-backed by DLMF but is not silently
-- imported into the constructed sine.  This distinction is exactly what the
-- perfect-conductor longitudinal mode search needs: indexed candidate modes
-- can be generated internally, while exhaustiveness still owes a same-object
-- classification weld.
------------------------------------------------------------------------

natMultiple :
  (real : R.ConstructedOrderedCompleteReal) →
  Nat → R.Real real → R.Real real
natMultiple real zero x = R.zero real
natMultiple real (suc n) x = R._+_ real (natMultiple real n x) x

zeroTimes :
  {real : R.ConstructedOrderedCompleteReal} →
  Ring.ConstructedRealRingNormalisationLaws real →
  (x : R.Real real) →
  R._*_ real (R.zero real) x ≡ R.zero real
zeroTimes {real} laws x =
  trans (R.mulComm real (R.zero real) x) (Ring.mulZeroRightLaw laws x)

sinNaturalMultiplePiZero :
  {real : R.ConstructedOrderedCompleteReal} →
  {exp : R.ConstructedRealExponential real} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (trig : Trig.TrigonometricPowerSeriesAuthority real exp) →
  (n : Nat) →
  Trig.sin trig (natMultiple real n (Trig.pi trig)) ≡ R.zero real
sinNaturalMultiplePiZero {real} laws trig zero = Trig.sinZero trig
sinNaturalMultiplePiZero {real} laws trig (suc n) =
  trans
    (Trig.sinAdd trig
      (natMultiple real n (Trig.pi trig))
      (Trig.pi trig))
    (trans
      (cong₂
        (R._+_ real)
        (cong
          (λ s → R._*_ real s (Trig.cos trig (Trig.pi trig)))
          (sinNaturalMultiplePiZero laws trig n))
        (cong
          (R._*_ real (Trig.cos trig (natMultiple real n (Trig.pi trig))))
          (Trig.sinPi trig)))
      (trans
        (cong₂
          (R._+_ real)
          (zeroTimes laws (Trig.cos trig (Trig.pi trig)))
          (Ring.mulZeroRightLaw laws
            (Trig.cos trig (natMultiple real n (Trig.pi trig)))))
        (R.addZeroLeft real (R.zero real))))

record ForwardIndexedSineMode
    {real : R.ConstructedOrderedCompleteReal}
    {exp : R.ConstructedRealExponential real}
    (laws : Ring.ConstructedRealRingNormalisationLaws real)
    (trig : Trig.TrigonometricPowerSeriesAuthority real exp)
    (n : Nat) : Set where
  field
    zeroReceipt :
      Trig.sin trig (natMultiple real n (Trig.pi trig)) ≡ R.zero real

open ForwardIndexedSineMode public

forwardIndexedSineMode :
  {real : R.ConstructedOrderedCompleteReal} →
  {exp : R.ConstructedRealExponential real} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (trig : Trig.TrigonometricPowerSeriesAuthority real exp) →
  (n : Nat) →
  ForwardIndexedSineMode laws trig n
forwardIndexedSineMode laws trig n = record
  { zeroReceipt = sinNaturalMultiplePiZero laws trig n }

record ReverseSineZeroClassificationWeld : Set₁ where
  field
    sourceAuthority : Source.SineZeroClassificationSourceAuthority
    sameSineObject : Set
    samePiObject : Set
    integerIndexTransport : Set
    reverseClassificationOnConstructedSine : Set

open ReverseSineZeroClassificationWeld public

data ForwardZerosAutomaticallyGiveReverseClassification : Set where

forwardDoesNotProveExhaustiveness :
  ForwardZerosAutomaticallyGiveReverseClassification → DASHI.Core.Prelude.⊥
forwardDoesNotProveExhaustiveness ()
