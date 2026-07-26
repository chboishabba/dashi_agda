module DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; _+_; -_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed

------------------------------------------------------------------------
-- Algebraic real-field owner.
--
-- The Fourier coefficient uses only field algebra.  Completeness/order of the
-- analytic real numbers belongs to the later PDE limit layer, not to the
-- finite coefficient definition.  No Navier--Stokes estimate is a field here.
------------------------------------------------------------------------

record RealField (r : Level) : Set (lsuc r) where
  field
    Carrier : Set r
    zero one : Carrier
    add multiply : Carrier → Carrier → Carrier
    negate inverse : Carrier → Carrier

    addAssociative : ∀ a b c → add (add a b) c ≡ add a (add b c)
    addCommutative : ∀ a b → add a b ≡ add b a
    addZeroLeft : ∀ a → add zero a ≡ a
    addInverseLeft : ∀ a → add (negate a) a ≡ zero

    multiplyAssociative : ∀ a b c →
      multiply (multiply a b) c ≡ multiply a (multiply b c)
    multiplyCommutative : ∀ a b → multiply a b ≡ multiply b a
    multiplyOneLeft : ∀ a → multiply one a ≡ a
    distributeLeft : ∀ a b c →
      multiply a (add b c) ≡ add (multiply a b) (multiply a c)

    negateInvolutive : ∀ a → negate (negate a) ≡ a
    negateZero : negate zero ≡ zero

open RealField public

------------------------------------------------------------------------
-- Literal complex numbers over the selected real field.
------------------------------------------------------------------------

record Complex {r : Level} (F : RealField r) : Set r where
  constructor complex
  field
    real imaginary : Carrier F

open Complex public

complexZero : ∀ {r} (F : RealField r) → Complex F
complexZero F = complex (zero F) (zero F)

complexOne : ∀ {r} (F : RealField r) → Complex F
complexOne F = complex (one F) (zero F)

complexI : ∀ {r} (F : RealField r) → Complex F
complexI F = complex (zero F) (one F)

complexAdd : ∀ {r} {F : RealField r} → Complex F → Complex F → Complex F
complexAdd {F = F} (complex ar ai) (complex br bi) =
  complex (add F ar br) (add F ai bi)

complexNegate : ∀ {r} {F : RealField r} → Complex F → Complex F
complexNegate {F = F} (complex ar ai) =
  complex (negate F ar) (negate F ai)

complexSubtract : ∀ {r} {F : RealField r} → Complex F → Complex F → Complex F
complexSubtract a b = complexAdd a (complexNegate b)

complexMultiply : ∀ {r} {F : RealField r} → Complex F → Complex F → Complex F
complexMultiply {F = F} (complex ar ai) (complex br bi) =
  complex
    (add F
      (multiply F ar br)
      (negate F (multiply F ai bi)))
    (add F
      (multiply F ar bi)
      (multiply F ai br))

complexConjugate : ∀ {r} {F : RealField r} → Complex F → Complex F
complexConjugate {F = F} (complex ar ai) =
  complex ar (negate F ai)

complexRealPart : ∀ {r} {F : RealField r} → Complex F → Complex F
complexRealPart {F = F} (complex ar ai) = complex ar (zero F)

realEmbed : ∀ {r} (F : RealField r) → Carrier F → Complex F
realEmbed F a = complex a (zero F)

complexConjugateInvolutive :
  ∀ {r} {F : RealField r} (z : Complex F) →
  complexConjugate (complexConjugate z) ≡ z
complexConjugateInvolutive {F = F} (complex ar ai)
  rewrite negateInvolutive F ai = refl

------------------------------------------------------------------------
-- Literal C^3.
------------------------------------------------------------------------

record Complex3 {r : Level} (F : RealField r) : Set r where
  constructor complex3
  field
    x y z : Complex F

open Complex3 public

complex3Zero : ∀ {r} (F : RealField r) → Complex3 F
complex3Zero F = complex3 (complexZero F) (complexZero F) (complexZero F)

complex3Add : ∀ {r} {F : RealField r} → Complex3 F → Complex3 F → Complex3 F
complex3Add (complex3 ax ay az) (complex3 bx by bz) =
  complex3
    (complexAdd ax bx)
    (complexAdd ay by)
    (complexAdd az bz)

complex3Negate : ∀ {r} {F : RealField r} → Complex3 F → Complex3 F
complex3Negate (complex3 ax ay az) =
  complex3 (complexNegate ax) (complexNegate ay) (complexNegate az)

complex3Subtract : ∀ {r} {F : RealField r} → Complex3 F → Complex3 F → Complex3 F
complex3Subtract a b = complex3Add a (complex3Negate b)

complex3Scale : ∀ {r} {F : RealField r} → Complex F → Complex3 F → Complex3 F
complex3Scale scalar (complex3 ax ay az) =
  complex3
    (complexMultiply scalar ax)
    (complexMultiply scalar ay)
    (complexMultiply scalar az)

complex3Conjugate : ∀ {r} {F : RealField r} → Complex3 F → Complex3 F
complex3Conjugate (complex3 ax ay az) =
  complex3
    (complexConjugate ax)
    (complexConjugate ay)
    (complexConjugate az)

bilinearDot3 : ∀ {r} {F : RealField r} → Complex3 F → Complex3 F → Complex F
bilinearDot3 (complex3 ax ay az) (complex3 bx by bz) =
  complexAdd
    (complexAdd (complexMultiply ax bx) (complexMultiply ay by))
    (complexMultiply az bz)

hermitianPairing3 : ∀ {r} {F : RealField r} → Complex3 F → Complex3 F → Complex F
hermitianPairing3 a b = bilinearDot3 (complex3Conjugate a) b

------------------------------------------------------------------------
-- Integer lattice embedding and exact Leray formula.
------------------------------------------------------------------------

record IntegerEmbedding {r : Level} (F : RealField r) : Set (lsuc r) where
  field
    embedInteger : ℤ → Carrier F
    embedZero : embedInteger (+ 0) ≡ zero F
    embedAdd : ∀ a b →
      embedInteger (a + b)
      ≡ add F (embedInteger a) (embedInteger b)
    embedNegate : ∀ a →
      embedInteger (- a)
      ≡ negate F (embedInteger a)

open IntegerEmbedding public

modeVector :
  ∀ {r} {F : RealField r} →
  IntegerEmbedding F → Z3.FourierMode → Complex3 F
modeVector {F = F} E k =
  complex3
    (realEmbed F (embedInteger E (Z3.kx k)))
    (realEmbed F (embedInteger E (Z3.ky k)))
    (realEmbed F (embedInteger E (Z3.kz k)))

record ModeInverseSquare
    {r : Level} (F : RealField r) (E : IntegerEmbedding F) :
    Set (lsuc r) where
  field
    inverseNormSquared : Z3.FourierMode → Carrier F
    normSquared : Z3.FourierMode → Carrier F

    normSquaredMeaning : ∀ k →
      normSquared k ≡
      add F
        (add F
          (multiply F
            (embedInteger E (Z3.kx k))
            (embedInteger E (Z3.kx k)))
          (multiply F
            (embedInteger E (Z3.ky k))
            (embedInteger E (Z3.ky k))))
        (multiply F
          (embedInteger E (Z3.kz k))
          (embedInteger E (Z3.kz k)))

    inverseLaw : ∀ k → Z3.NonZeroMode k →
      multiply F (inverseNormSquared k) (normSquared k) ≡ one F

open ModeInverseSquare public

lerayProject3 :
  ∀ {r} {F : RealField r}
    (E : IntegerEmbedding F)
    (I : ModeInverseSquare F E) →
  Z3.FourierMode → Complex3 F → Complex3 F
lerayProject3 {F = F} E I k value =
  complex3Subtract value
    (complex3Scale
      (complexMultiply
        (realEmbed F (inverseNormSquared I k))
        (bilinearDot3 (modeVector E k) value))
      (modeVector E k))

------------------------------------------------------------------------
-- Exact instantiation of the signed coefficient interface.
------------------------------------------------------------------------

complex3VelocityGalerkinLaws :
  ∀ {r} (F : RealField r)
    (E : IntegerEmbedding F)
    (I : ModeInverseSquare F E) →
  Signed.VelocityGalerkinLaws
    Z3.FourierMode
    (Complex3 F)
    (Complex F)
complex3VelocityGalerkinLaws F E I = record
  { scalarZero = complexZero F
  ; imaginaryUnit = complexI F
  ; scalarAdd = complexAdd
  ; scalarMultiply = complexMultiply
  ; scalarNegate = complexNegate
  ; conjugate = complexConjugate
  ; realPart = complexRealPart
  ; vectorAdd = complex3Add
  ; vectorScale = complex3Scale
  ; bilinearDot = bilinearDot3
  ; hermitianPairing = hermitianPairing3
  ; waveVector = modeVector E
  ; lerayProject = lerayProject3 E I
  }

complex3CarrierConstructed : Bool
complex3CarrierConstructed = true

complex3CarrierConstructedIsTrue : complex3CarrierConstructed ≡ true
complex3CarrierConstructedIsTrue = refl

exactSignedCoefficientInstantiatedOnComplex3 : Bool
exactSignedCoefficientInstantiatedOnComplex3 = true

exactSignedCoefficientInstantiatedOnComplex3IsTrue :
  exactSignedCoefficientInstantiatedOnComplex3 ≡ true
exactSignedCoefficientInstantiatedOnComplex3IsTrue = refl
