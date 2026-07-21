module Verification.JacobianCounterexampleScalarExtension where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Verification.JacobianCounterexampleKernel as J
  using
    ( Poly3
    ; constant
    ; xVar
    ; yVar
    ; zVar
    ; _+P_
    ; _*P_
    ; negP
    ; evalP
    ; Point3
    ; point3
    ; xCoordinate
    ; yCoordinate
    ; zCoordinate
    ; PolynomialMap3
    ; firstCoordinate
    ; secondCoordinate
    ; thirdCoordinate
    ; alpogePolynomialMap
    ; jacobianDeterminantPolynomial
    ; F
    ; pZero
    ; pPositive
    ; target
    ; pZeroPositiveCollision
    ; zeroNotOne
    ; zeroQ
    ; oneR
    ; minusTwoQ
    ; _≢_
    ; Injective
    ; collisionImpliesNotInjective
    )

------------------------------------------------------------------------
-- Faithful rational scalar extensions.

record RationalScalarExtension : Set₁ where
  field
    Scalar : Set
    zeroS oneS : Scalar
    _+S_ _*S_ : Scalar → Scalar → Scalar
    negS : Scalar → Scalar
    embed : ℚ → Scalar
    embedInjective : ∀ {p q} → embed p ≡ embed q → p ≡ q
    embedZero : embed J.zeroQ ≡ zeroS
    embedOne : embed J.oneQ ≡ oneS
    embedAdd : (p q : ℚ) → embed (p J.+ q) ≡ embed p +S embed q
    embedMul : (p q : ℚ) → embed (p J.* q) ≡ embed p *S embed q
    embedNeg : (p : ℚ) → embed (J.- p) ≡ negS (embed p)

open RationalScalarExtension public

cong₂ :
  ∀ {A B C : Set} (f : A → B → C)
    {x x' : A} {y y' : B} →
  x ≡ x' → y ≡ y' →
  f x y ≡ f x' y'
cong₂ f refl refl = refl

record ExtendedPoint3 (E : RationalScalarExtension) : Set where
  constructor extendedPoint3
  field
    xS yS zS : Scalar E

open ExtendedPoint3 public

liftPoint :
  (E : RationalScalarExtension) →
  Point3 →
  ExtendedPoint3 E
liftPoint E p =
  extendedPoint3
    (embed E (xCoordinate p))
    (embed E (yCoordinate p))
    (embed E (zCoordinate p))

evalExtended :
  (E : RationalScalarExtension) →
  Poly3 →
  Scalar E → Scalar E → Scalar E →
  Scalar E
evalExtended E (constant c) x y z = embed E c
evalExtended E xVar x y z = x
evalExtended E yVar x y z = y
evalExtended E zVar x y z = z
evalExtended E (p +P q) x y z =
  _+S_ E (evalExtended E p x y z) (evalExtended E q x y z)
evalExtended E (p *P q) x y z =
  _*S_ E (evalExtended E p x y z) (evalExtended E q x y z)
evalExtended E (negP p) x y z =
  negS E (evalExtended E p x y z)

evalExtendedCommutes :
  (E : RationalScalarExtension) →
  (p : Poly3) →
  (x y z : ℚ) →
  evalExtended E p (embed E x) (embed E y) (embed E z)
    ≡ embed E (evalP p x y z)
evalExtendedCommutes E (constant c) x y z = refl
evalExtendedCommutes E xVar x y z = refl
evalExtendedCommutes E yVar x y z = refl
evalExtendedCommutes E zVar x y z = refl
evalExtendedCommutes E (p +P q) x y z =
  trans
    (cong₂ (_+S_ E)
      (evalExtendedCommutes E p x y z)
      (evalExtendedCommutes E q x y z))
    (sym (embedAdd E (evalP p x y z) (evalP q x y z)))
evalExtendedCommutes E (p *P q) x y z =
  trans
    (cong₂ (_*S_ E)
      (evalExtendedCommutes E p x y z)
      (evalExtendedCommutes E q x y z))
    (sym (embedMul E (evalP p x y z) (evalP q x y z)))
evalExtendedCommutes E (negP p) x y z =
  trans
    (cong (negS E) (evalExtendedCommutes E p x y z))
    (sym (embedNeg E (evalP p x y z)))

applyExtendedMap3 :
  (E : RationalScalarExtension) →
  PolynomialMap3 →
  ExtendedPoint3 E →
  ExtendedPoint3 E
applyExtendedMap3 E map (extendedPoint3 x y z) =
  extendedPoint3
    (evalExtended E (firstCoordinate map) x y z)
    (evalExtended E (secondCoordinate map) x y z)
    (evalExtended E (thirdCoordinate map) x y z)

extendedPoint3-ext :
  ∀ {E : RationalScalarExtension}
    {x x' y y' z z' : Scalar E} →
  x ≡ x' → y ≡ y' → z ≡ z' →
  extendedPoint3 {E} x y z ≡ extendedPoint3 {E} x' y' z'
extendedPoint3-ext refl refl refl = refl

applyExtendedCommutes :
  (E : RationalScalarExtension) →
  (map : PolynomialMap3) →
  (p : Point3) →
  applyExtendedMap3 E map (liftPoint E p)
    ≡ liftPoint E (J.applyPolynomialMap3 map p)
applyExtendedCommutes E map (point3 x y z) =
  extendedPoint3-ext
    (evalExtendedCommutes E (firstCoordinate map) x y z)
    (evalExtendedCommutes E (secondCoordinate map) x y z)
    (evalExtendedCommutes E (thirdCoordinate map) x y z)

extendedF :
  (E : RationalScalarExtension) →
  ExtendedPoint3 E →
  ExtendedPoint3 E
extendedF E = applyExtendedMap3 E alpogePolynomialMap

liftedZeroNotPositive :
  (E : RationalScalarExtension) →
  liftPoint E pZero ≢ liftPoint E pPositive
liftedZeroNotPositive E equality =
  zeroNotOne
    (embedInjective E
      (cong xS equality))

liftedCollision :
  (E : RationalScalarExtension) →
  extendedF E (liftPoint E pZero)
    ≡ extendedF E (liftPoint E pPositive)
liftedCollision E =
  trans
    (applyExtendedCommutes E alpogePolynomialMap pZero)
    (trans
      (cong (liftPoint E) pZeroPositiveCollision)
      (sym (applyExtendedCommutes E alpogePolynomialMap pPositive)))

extendedF-notInjective :
  (E : RationalScalarExtension) →
  J.¬ Injective (extendedF E)
extendedF-notInjective E =
  collisionImpliesNotInjective
    (extendedF E)
    (liftedZeroNotPositive E)
    (liftedCollision E)

------------------------------------------------------------------------
-- Determinant transfer is a ring-identity theorem, not a consequence of the
-- collision alone.  A concrete scalar foundation, such as a complex-number
-- implementation, supplies this authority once its ring normalization lane is
-- connected.

jacobianDeterminantExtendedAt :
  (E : RationalScalarExtension) →
  ExtendedPoint3 E →
  Scalar E
jacobianDeterminantExtendedAt E (extendedPoint3 x y z) =
  evalExtended E (jacobianDeterminantPolynomial alpogePolynomialMap) x y z

record KellerIdentityTransfer
    (E : RationalScalarExtension)
    : Set₁ where
  field
    determinantIdentityAllScalars :
      (p : ExtendedPoint3 E) →
      jacobianDeterminantExtendedAt E p ≡ embed E minusTwoQ
    determinantConstantNonzero : embed E minusTwoQ ≢ zeroS E

record ScalarExtensionCounterexample
    (E : RationalScalarExtension)
    : Set₁ where
  constructor scalarExtensionCounterexample
  field
    determinantAuthority : KellerIdentityTransfer E
    noninjective : J.¬ Injective (extendedF E)

makeScalarExtensionCounterexample :
  (E : RationalScalarExtension) →
  KellerIdentityTransfer E →
  ScalarExtensionCounterexample E
makeScalarExtensionCounterexample E determinantAuthority =
  scalarExtensionCounterexample
    determinantAuthority
    (extendedF-notInjective E)

record ComplexCounterexampleAuthority : Set₁ where
  field
    complexScalarExtension : RationalScalarExtension
    carrierIsComplexNumbers : Set
    determinantTransfer : KellerIdentityTransfer complexScalarExtension

complexAuthorityGivesCounterexample :
  (authority : ComplexCounterexampleAuthority) →
  ScalarExtensionCounterexample
    (ComplexCounterexampleAuthority.complexScalarExtension authority)
complexAuthorityGivesCounterexample authority =
  makeScalarExtensionCounterexample
    (ComplexCounterexampleAuthority.complexScalarExtension authority)
    (ComplexCounterexampleAuthority.determinantTransfer authority)

record ScalarExtensionReceipt : Set where
  constructor mkScalarExtensionReceipt
  field
    rationalCollisionLiftsToEveryFaithfulExtension : Bool
    complexCarrierFabricatedHere : Bool
    complexCarrierFabricatedHereIsFalse : complexCarrierFabricatedHere ≡ false
    determinantTransferFabricatedFromCollision : Bool
    determinantTransferFabricatedFromCollisionIsFalse :
      determinantTransferFabricatedFromCollision ≡ false
    interpretation : String

scalarExtensionReceipt : ScalarExtensionReceipt
scalarExtensionReceipt =
  mkScalarExtensionReceipt
    true
    false refl
    false refl
    "the exact rational collision lifts to every injective rational scalar extension; an actual complex carrier and universal determinant identity are supplied by an explicit complex/ring-normalization authority"
