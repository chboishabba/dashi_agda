module DASHI.Mathematics.Symmetry.TetragonalPrimitiveSeitzExact where

-- Primitive tetragonal (symmorphic P4/mmm-type) affine-coordinate
-- candidate. Point group D4h, translation lattice Z^3.
--
-- Classical Seitz semidirect multiplication:
--   (g,t)(h,u) = (gh, t + g u)
-- on points p: (g,t) p = g p + t.
-- The full group law still needs the coordinate actCompose proof;
-- none is asserted by mere construction of these operations.
-- This does not model diamond Fd-3m fractional translations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; -_; +_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; ⊝_; solve)
import Data.Integer.Properties as IntP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Mathematics.Symmetry.TetragonalSignedCoordinateGroupActionExact as CoordGroup
import DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact as Coord
import DASHI.Mathematics.Symmetry.TetragonalIntegerMetricPairingExact as Metric
import DASHI.Mathematics.Symmetry.TetragonalD4hFullActionExact as Full
import DASHI.Physics.Closure.NSIntegerFourierLattice as NS
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.TetragonalFourierLatticeBridgeExact as F

record PrimitiveSeitz : Set where
  constructor seitz
  field
    linearPart : D.D4h
    integerTranslation : NS.FourierMode
open PrimitiveSeitz public

seitzIdentity : PrimitiveSeitz
seitzIdentity = seitz D.identity NS.zeroMode

seitzMultiply : PrimitiveSeitz → PrimitiveSeitz → PrimitiveSeitz
seitzMultiply (seitz g t) (seitz h u) =
  seitz (D.compose g h) (NS.addMode t (F.actMode g u))

seitzApply : PrimitiveSeitz → NS.FourierMode → NS.FourierMode
seitzApply (seitz g t) p =
  NS.addMode t (F.actMode g p)

pureTranslation : NS.FourierMode → PrimitiveSeitz
pureTranslation t = seitz D.identity t

purePointOperation : D.D4h → PrimitiveSeitz
purePointOperation g = seitz g NS.zeroMode

seitzTranslationApplies :
  (t : NS.FourierMode) (p : NS.FourierMode) →
  seitzApply (pureTranslation t) p ≡ NS.addMode t p
seitzTranslationApplies (NS.mode tx ty tz) (NS.mode x y z) = refl

-- A translation does not alter the reciprocal wavevector *index*.
-- A Bloch state nonetheless acquires a translation-dependent phase,
-- which is not modelled by this raw integer-lattice action.
reciprocalIndex : PrimitiveSeitz → NS.FourierMode → NS.FourierMode
reciprocalIndex s k = F.actMode (linearPart s) k

reciprocalTranslationIsIdentity :
  (t : NS.FourierMode) (k : NS.FourierMode) →
  reciprocalIndex (pureTranslation t) k ≡ k
reciprocalTranslationIsIdentity t (NS.mode kx ky kz) = refl

-- A mathematical primitive lattice Z³ with a tP metric is not a
-- specific experimentally identified solid. Atomic 369 decoration,
-- tI centring, Bloch phases, magnetic groups, and fractional
-- nonsymmorphic translations remain independently typed consumers.

-- Record equality is introduced only after each component is proved.
modeExt :
  ∀ {p q : NS.FourierMode} →
  NS.kx p ≡ NS.kx q →
  NS.ky p ≡ NS.ky q →
  NS.kz p ≡ NS.kz q →
  p ≡ q
modeExt {NS.mode x y z} {NS.mode .x .y .z} refl refl refl = refl

addModeAssociative :
  (p q r : NS.FourierMode) →
  NS.addMode (NS.addMode p q) r ≡
  NS.addMode p (NS.addMode q r)
addModeAssociative (NS.mode x y z) (NS.mode u v w) (NS.mode a b c) =
  modeExt (IntP.+-assoc x u a)
          (IntP.+-assoc y v b)
          (IntP.+-assoc z w c)

zeroLeft :
  (p : NS.FourierMode) → NS.addMode NS.zeroMode p ≡ p
zeroLeft (NS.mode x y z) =
  modeExt (IntP.+-identityˡ x)
          (IntP.+-identityˡ y)
          (IntP.+-identityˡ z)

actModeIdentity :
  (p : NS.FourierMode) → F.actMode D.identity p ≡ p
actModeIdentity p =
  trans (cong F.toMode
            (CoordGroup.actIdentity Metric.integerSignedCarrier (F.fromMode p)))
        (F.modeRoundTrip p)

actModeCompose :
  (g h : D.D4h) (p : NS.FourierMode) →
  F.actMode (D.compose g h) p ≡
  F.actMode g (F.actMode h p)
actModeCompose g h p =
  trans
    (cong F.toMode
      (CoordGroup.actCompose Metric.integerSignedCarrier
         g h (F.fromMode p)))
    (cong (λ v → F.toMode (Coord.act Metric.integerSignedCarrier g v))
      (sym (F.tripleRoundTrip
        (Coord.act Metric.integerSignedCarrier h (F.fromMode p)))))

seitzIdentityActs :
  (p : NS.FourierMode) → seitzApply seitzIdentity p ≡ p
seitzIdentityActs p =
  trans (cong (NS.addMode NS.zeroMode) (actModeIdentity p))
        (zeroLeft p)

seitzApplyComposes :
  (s t : PrimitiveSeitz) (p : NS.FourierMode) →
  seitzApply (seitzMultiply s t) p ≡
  seitzApply s (seitzApply t p)
seitzApplyComposes (seitz g u) (seitz h v) p =
  trans
    (cong (NS.addMode (NS.addMode u (F.actMode g v)))
          (actModeCompose g h p))
    (trans
      (addModeAssociative u (F.actMode g v) (F.actMode g (F.actMode h p)))
      (cong (NS.addMode u)
        (sym (F.actModeAdd g v (F.actMode h p)))))

seitzCong :
  ∀ {g h : D.D4h} {u v : NS.FourierMode} →
  g ≡ h → u ≡ v → seitz g u ≡ seitz h v
seitzCong refl refl = refl

-- Affine semidirect-product multiplication is associative on the
-- actual (infinite) Z³ carrier, using the existing finite D4h theorem.
seitzAssociative :
  (s t u : PrimitiveSeitz) →
  seitzMultiply (seitzMultiply s t) u ≡
  seitzMultiply s (seitzMultiply t u)
seitzAssociative (seitz g a) (seitz h b) (seitz k c) =
  seitzCong
    (Full.associative g h k)
    (trans
      (cong (NS.addMode (NS.addMode a (F.actMode g b)))
        (actModeCompose g h c))
      (trans
        (addModeAssociative a (F.actMode g b)
                              (F.actMode g (F.actMode h c)))
        (cong (NS.addMode a)
          (sym (F.actModeAdd g b (F.actMode h c))))))

-- Group inverse / two-sided identity as elements and nonlinear
-- Bloch translation phases are separate receipts. Action identity
-- and multiplication, and operation associativity, are above.

-- Group identity and inverse laws (not merely an affine action).
zeroRight :
  (p : NS.FourierMode) → NS.addMode p NS.zeroMode ≡ p
zeroRight (NS.mode x y z) =
  modeExt (IntP.+-identityʳ x)
          (IntP.+-identityʳ y)
          (IntP.+-identityʳ z)

actModeZero :
  (g : D.D4h) → F.actMode g NS.zeroMode ≡ NS.zeroMode
actModeZero (D.element D.q0 false false) = refl
actModeZero (D.element D.q0 false true) = refl
actModeZero (D.element D.q0 true false) = refl
actModeZero (D.element D.q0 true true) = refl
actModeZero (D.element D.q1 false false) = refl
actModeZero (D.element D.q1 false true) = refl
actModeZero (D.element D.q1 true false) = refl
actModeZero (D.element D.q1 true true) = refl
actModeZero (D.element D.q2 false false) = refl
actModeZero (D.element D.q2 false true) = refl
actModeZero (D.element D.q2 true false) = refl
actModeZero (D.element D.q2 true true) = refl
actModeZero (D.element D.q3 false false) = refl
actModeZero (D.element D.q3 false true) = refl
actModeZero (D.element D.q3 true false) = refl
actModeZero (D.element D.q3 true true) = refl

leftSeitzIdentity :
  (s : PrimitiveSeitz) → seitzMultiply seitzIdentity s ≡ s
leftSeitzIdentity (seitz g t) =
  seitzCong
    (D.identityLeft g)
    (trans
      (cong (NS.addMode NS.zeroMode) (actModeIdentity t))
      (zeroLeft t))

rightSeitzIdentity :
  (s : PrimitiveSeitz) → seitzMultiply s seitzIdentity ≡ s
rightSeitzIdentity (seitz g t) =
  seitzCong
    (D.identityRight g)
    (trans
      (cong (NS.addMode t) (actModeZero g))
      (zeroRight t))

scalarNegativeCancellationLeft :
  (x : ℤ) → (- x) + x ≡ + 0
scalarNegativeCancellationLeft x =
  RingZ.solve 1
    (λ x → (⊝ x ⊕ x , Κ (+ 0)))
    refl x

scalarNegativeCancellationRight :
  (x : ℤ) → x + (- x) ≡ + 0
scalarNegativeCancellationRight x =
  RingZ.solve 1
    (λ x → (x ⊕ ⊝ x , Κ (+ 0)))
    refl x

negativeModeCancelsLeft :
  (p : NS.FourierMode) →
  NS.addMode (NS.negateMode p) p ≡ NS.zeroMode
negativeModeCancelsLeft (NS.mode x y z) =
  modeExt
    (scalarNegativeCancellationLeft x)
    (scalarNegativeCancellationLeft y)
    (scalarNegativeCancellationLeft z)

negativeModeCancelsRight :
  (p : NS.FourierMode) →
  NS.addMode p (NS.negateMode p) ≡ NS.zeroMode
negativeModeCancelsRight (NS.mode x y z) =
  modeExt
    (scalarNegativeCancellationRight x)
    (scalarNegativeCancellationRight y)
    (scalarNegativeCancellationRight z)

seitzInverse : PrimitiveSeitz → PrimitiveSeitz
seitzInverse (seitz g t) =
  seitz (D.inverse g)
        (F.actMode (D.inverse g) (NS.negateMode t))

leftSeitzInverse :
  (s : PrimitiveSeitz) →
  seitzMultiply (seitzInverse s) s ≡ seitzIdentity
leftSeitzInverse (seitz g t) =
  seitzCong
    (D.inverseLeft g)
    (trans
      (sym (F.actModeAdd (D.inverse g) (NS.negateMode t) t))
      (trans
        (cong (F.actMode (D.inverse g)) (negativeModeCancelsLeft t))
        (actModeZero (D.inverse g))))

rightSeitzInverse :
  (s : PrimitiveSeitz) →
  seitzMultiply s (seitzInverse s) ≡ seitzIdentity
rightSeitzInverse (seitz g t) =
  seitzCong
    (D.inverseRight g)
    (trans
      (cong (NS.addMode t)
        (sym (actModeCompose g (D.inverse g) (NS.negateMode t))))
      (trans
        (cong (λ h → NS.addMode t
          (F.actMode h (NS.negateMode t))) (D.inverseRight g))
        (trans
          (cong (NS.addMode t) (actModeIdentity (NS.negateMode t)))
          (negativeModeCancelsRight t))))

-- P4/mmm-type affine group closure is now expressed by proof terms:
-- semidirect associativity, identity and inverse, plus the left
-- affine action laws. Kernel typechecking remains a separate receipt.
