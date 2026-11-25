module DASHI.Wikimedia.ShemNonlocalHolonomyExact where

-- H26. Exact root-transport/chord reconciliation; candidate geometry,
-- not a source-attested KeyShoe law. No assumption of global source truth.
open import DASHI.Core.Prelude
open import DASHI.Wikimedia.KeyShoeNativeFieldIncidenceExact using (Point; inverse)
open import DASHI.Wikimedia.KeyShoeFieldLawMovingFrameExact
  using (Frame; frameEncode; frameDecode; frameEncodeDecode; frameDecodeEncode)

-- Coordinate change representing the SAME physical payload at two sites.
-- Distinct from frameTransport, which preserves normalized coordinates.
physicalChange : Frame → Frame → Point → Point
physicalChange f g r = frameDecode g (frameEncode f r)

physicalCompose : (f g h : Frame) (r : Point) →
  physicalChange g h (physicalChange f g r) ≡ physicalChange f h r
physicalCompose f g h r
  rewrite frameEncodeDecode g (frameEncode f r) = refl

physicalLoop : (f g : Frame) (r : Point) →
  physicalChange g f (physicalChange f g r) ≡ r
physicalLoop f g r =
  trans (physicalCompose f g f r) (frameDecodeEncode f r)

-- Chord e from i to j, tree maps P_i/P_j from a common root.
-- A chord is satisfied iff its pulled-back holonomy fixes the root.
-- Explicit left and right inverse arguments reuse existing path inverses;
-- this lemma is independent of the particular field arithmetic.
rootHolonomy : {A : Set} →
  (Pi Pj PjBack E : A → A) → A → A
rootHolonomy Pi Pj PjBack E r = PjBack (E (Pi r))

chordToFixed : {A : Set} →
  (Pi Pj PjBack E : A → A) →
  (leftInv : (x : A) → PjBack (Pj x) ≡ x) →
  (r : A) → E (Pi r) ≡ Pj r →
  rootHolonomy Pi Pj PjBack E r ≡ r
chordToFixed Pi Pj PjBack E leftInv r edge =
  trans (cong PjBack edge) (leftInv r)

fixedToChord : {A : Set} →
  (Pi Pj PjBack E : A → A) →
  (rightInv : (x : A) → Pj (PjBack x) ≡ x) →
  (r : A) → rootHolonomy Pi Pj PjBack E r ≡ r →
  E (Pi r) ≡ Pj r
fixedToChord Pi Pj PjBack E rightInv r fixed =
  trans (sym (rightInv (E (Pi r)))) (cong Pj fixed)

-- One twisted return in a physical chart: source root-coordinate
-- fixed point iff the intermediate normalized coordinate is inversion-fixed.
twistedRoot : Frame → Point → Point
twistedRoot f x = frameEncode f (inverse (frameDecode f x))

twistedFixedToLocal : (f : Frame) (x : Point) →
  twistedRoot f x ≡ x →
  inverse (frameDecode f x) ≡ frameDecode f x
twistedFixedToLocal f x fixed =
  trans (sym (frameDecodeEncode f (inverse (frameDecode f x))))
    (cong (frameDecode f) fixed)

localFixedToTwisted : (f : Frame) (x : Point) →
  inverse (frameDecode f x) ≡ frameDecode f x →
  twistedRoot f x ≡ x
localFixedToTwisted f x fixed =
  trans (cong (frameEncode f) fixed) (frameEncodeDecode f x)
