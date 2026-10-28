module DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryLocalFibreActionExact where

------------------------------------------------------------------------
-- NATIVE TERNARY END: FINITE-LEVEL C3-VALUED FIBRE ACTIONS
--
-- Existing owner: AlexanderHornedNativeBalancedTernaryEndTowerExact.
-- Hatcher's ORIGINAL meridian geometry is BINARY (3*2^n generators).
-- This native ternary address tower is DISTINCT (3*3^n cells).
-- The fibre translation carrier is Map(K3_n,C3), |K3_n|=3*3^n.
--
-- At n=2: 27 address cells, Map(K3_2,C3) has 3^27 states.
-- Those functions form a pointwise ABELIAN GROUP and act faithfully by
-- translations on ternary fields. The external C3 sector rotation acts
-- on functions by inverse pullback. Together they have a finite
-- semidirect-product ACTION with a precise component multiplication.
--
-- We prove the generic *pointwise* group/action laws, pullback
-- injectivity, refinement equivariance and coherent-end evaluation.
-- No function extensionality postulate is used. Full equality of
-- functions needs extensional equality or a finite-table code.
--
-- This is NOT the exterior orbifold π1 = (G_A*G_A*G_A) ⋊ C3.
-- No actual wild embedding, continuous π1, Galois action, gauge
-- connection or Monster 3B representation is created here.
--
-- Provenance: Hatcher AT 2B.2 (binary horn source), classical
-- permutation wreath product definition, existing DASHI C3 + end
-- owners. New proof ownership limited to these finite exact adapters.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Cognition.RecursiveFibreTower as Tower

Level : Nat → Set
Level = End.BalancedLevel

Gauge : Nat → Set
Gauge n = Level n → C3.C3

Field : Nat → Set
Field = Gauge

pointwise : ∀ {n} → Gauge n → Gauge n → Set
pointwise {n} f g = (x : Level n) → f x ≡ g x

zeroGauge : ∀ n → Gauge n
zeroGauge n _ = C3.c0

addGauge : ∀ {n} → Gauge n → Gauge n → Gauge n
addGauge f g x = C3._∙_ (f x) (g x)

negateGauge : ∀ {n} → Gauge n → Gauge n
negateGauge f x = C3.inverse (f x)

pointwiseAddAssociative :
  ∀ {n} (f g h : Gauge n) (x : Level n) →
  addGauge (addGauge f g) h x
    ≡ addGauge f (addGauge g h) x
pointwiseAddAssociative f g h x =
  C3.associative (f x) (g x) (h x)

pointwiseLeftUnit :
  ∀ {n} (f : Gauge n) (x : Level n) →
  addGauge (zeroGauge n) f x ≡ f x
pointwiseLeftUnit f x = C3.leftIdentity (f x)

pointwiseRightUnit :
  ∀ {n} (f : Gauge n) (x : Level n) →
  addGauge f (zeroGauge n) x ≡ f x
pointwiseRightUnit f x = C3.rightIdentity (f x)

pointwiseInverse :
  ∀ {n} (f : Gauge n) (x : Level n) →
  addGauge (negateGauge f) f x ≡ C3.c0
pointwiseInverse f x = C3.inverseLeft (f x)

commutativeC3 : (a b : C3.C3) → C3._∙_ a b ≡ C3._∙_ b a
commutativeC3 C3.c0 C3.c0 = refl
commutativeC3 C3.c0 C3.c1 = refl
commutativeC3 C3.c0 C3.c2 = refl
commutativeC3 C3.c1 C3.c0 = refl
commutativeC3 C3.c1 C3.c1 = refl
commutativeC3 C3.c1 C3.c2 = refl
commutativeC3 C3.c2 C3.c0 = refl
commutativeC3 C3.c2 C3.c1 = refl
commutativeC3 C3.c2 C3.c2 = refl

pointwiseAddCommutative :
  ∀ {n} (f g : Gauge n) (x : Level n) →
  addGauge f g x ≡ addGauge g f x
pointwiseAddCommutative f g x = commutativeC3 (f x) (g x)

translate : ∀ {n} → Gauge n → Field n → Field n
translate = addGauge

translationActionComposition :
  ∀ {n} (g h : Gauge n) (f : Field n) (x : Level n) →
  translate (addGauge g h) f x
    ≡ translate g (translate h f) x
translationActionComposition g h f x =
  C3.associative (g x) (h x) (f x)

translationActionIdentity :
  ∀ {n} (f : Field n) (x : Level n) →
  translate (zeroGauge n) f x ≡ f x
translationActionIdentity = pointwiseLeftUnit

-- Translation acts faithfully: if g acts trivially on the ZERO field,
-- then g is pointwise trivial, without global function extensionality.
translationFaithful :
  ∀ {n} (g : Gauge n) →
  ((x : Level n) →
    translate g (zeroGauge n) x ≡ zeroGauge n x) →
  (x : Level n) → g x ≡ C3.c0
translationFaithful g actsAsIdentity x =
  trans (sym (C3.rightIdentity (g x))) (actsAsIdentity x)

------------------------------------------------------------------------
-- The projection has an explicit zero-trit section; hence the induced
-- pullback Gauge_n -> Gauge_(n+1) is INJECTIVE (pointwise).
------------------------------------------------------------------------

zeroSection : (n : Nat) → Level n → Level (suc n)
zeroSection n (c , xs) = c , End.snoc xs Trit.zero

projectZeroSection :
  (n : Nat) (x : Level n) →
  End.balancedProjection n (zeroSection n x) ≡ x
projectZeroSection n (c , xs) =
  cong (λ ys → (c , ys)) (End.dropLastSnoc xs Trit.zero)

pullback : (n : Nat) → Gauge n → Gauge (suc n)
pullback n g x = g (End.balancedProjection n x)

pullbackPreservesZero :
  ∀ n (x : Level (suc n)) →
  pullback n (zeroGauge n) x ≡ zeroGauge (suc n) x
pullbackPreservesZero n x = refl

pullbackPreservesAddition :
  ∀ n (g h : Gauge n) (x : Level (suc n)) →
  pullback n (addGauge g h) x
    ≡ addGauge (pullback n g) (pullback n h) x
pullbackPreservesAddition n g h x = refl

pullbackPreservesInverse :
  ∀ n (g : Gauge n) (x : Level (suc n)) →
  pullback n (negateGauge g) x
    ≡ negateGauge (pullback n g) x
pullbackPreservesInverse n g x = refl

pullbackFaithful :
  ∀ n (g h : Gauge n) →
  pointwise (pullback n g) (pullback n h) →
  pointwise g h
pullbackFaithful n g h same x
  rewrite projectZeroSection n x =
  same (zeroSection n x)

pullbackPreservesTranslation :
  ∀ n (g : Gauge n) (f : Field n) (x : Level (suc n)) →
  pullback n (translate g f) x
    ≡ translate (pullback n g) (pullback n f) x
pullbackPreservesTranslation n g f x = refl

------------------------------------------------------------------------
-- External three-SECTOR rotation on addresses. Use inverse pullback
-- on fields: (r.f)(x) = f(r^-1.x). The order of inverse is essential.
------------------------------------------------------------------------

rotatePoint : (n : Nat) → C3.C3 → Level n → Level n
rotatePoint n C3.c0 x = x
rotatePoint n C3.c1 x = End.rotateBalancedLevel n x
rotatePoint n C3.c2 x =
  End.rotateBalancedLevel n (End.rotateBalancedLevel n x)

rotatePointComposition :
  ∀ n (r s : C3.C3) (x : Level n) →
  rotatePoint n (C3._∙_ r s) x
    ≡ rotatePoint n r (rotatePoint n s x)
rotatePointComposition n C3.c0 s x = refl
rotatePointComposition n C3.c1 C3.c0 x = refl
rotatePointComposition n C3.c1 C3.c1 x = refl
rotatePointComposition n C3.c1 C3.c2 x =
  sym (End.balancedRotationCubed n x)
rotatePointComposition n C3.c2 C3.c0 x = refl
rotatePointComposition n C3.c2 C3.c1 x =
  sym (End.balancedRotationCubed n x)
rotatePointComposition n C3.c2 C3.c2 x =
  sym (cong (End.rotateBalancedLevel n)
    (End.balancedRotationCubed n x))

-- The inverse sector action is a genuine three-valued group action
-- on functions; pointwise composition avoids function extensionality.
rotateField : (n : Nat) → C3.C3 → Gauge n → Gauge n
rotateField n r f x =
  f (rotatePoint n (C3.inverse r) x)

rotateFieldIdentity :
  ∀ n (f : Gauge n) (x : Level n) →
  rotateField n C3.c0 f x ≡ f x
rotateFieldIdentity n f x = refl

rotateFieldComposition :
  ∀ n (r s : C3.C3) (f : Gauge n) (x : Level n) →
  rotateField n (C3._∙_ r s) f x
  ≡ rotateField n r (rotateField n s f) x
rotateFieldComposition n C3.c0 s f x = refl
rotateFieldComposition n C3.c1 C3.c0 f x = refl
rotateFieldComposition n C3.c1 C3.c1 f x =
  cong f
    (sym (cong (End.rotateBalancedLevel n)
      (End.balancedRotationCubed n x)))
rotateFieldComposition n C3.c1 C3.c2 f x =
  cong f (sym (End.balancedRotationCubed n x))
rotateFieldComposition n C3.c2 C3.c0 f x = refl
rotateFieldComposition n C3.c2 C3.c1 f x =
  cong f (sym (End.balancedRotationCubed n x))
rotateFieldComposition n C3.c2 C3.c2 f x = refl

rotateFieldPreservesAddition :
  ∀ n (r : C3.C3) (g h : Gauge n) (x : Level n) →
  rotateField n r (addGauge g h) x
  ≡ addGauge (rotateField n r g) (rotateField n r h) x
rotateFieldPreservesAddition n r g h x = refl

rotateFieldPreservesZero :
  ∀ n (r : C3.C3) (x : Level n) →
  rotateField n r (zeroGauge n) x ≡ C3.c0
rotateFieldPreservesZero n r x = refl

projectRotatePointSquare :
  ∀ n (r : C3.C3) (x : Level (suc n)) →
  End.balancedProjection n (rotatePoint (suc n) r x)
    ≡ rotatePoint n r (End.balancedProjection n x)
projectRotatePointSquare n C3.c0 x = refl
projectRotatePointSquare n C3.c1 x =
  End.rotateBalancedProjectionSquare n x
projectRotatePointSquare n C3.c2 x =
  trans
    (End.rotateBalancedProjectionSquare n
      (End.rotateBalancedLevel (suc n) x))
    (cong (End.rotateBalancedLevel n)
      (End.rotateBalancedProjectionSquare n x))

pullbackRotateEquivariant :
  ∀ n (r : C3.C3) (g : Gauge n) (x : Level (suc n)) →
  pullback n (rotateField n r g) x
  ≡ rotateField (suc n) r (pullback n g) x
pullbackRotateEquivariant n r g x =
  cong g (sym (projectRotatePointSquare n (C3.inverse r) x))

------------------------------------------------------------------------
-- Semidirect PRODUCT ACTION, not Hatcher's orbifold fundamental group.
-- Multiplication is (g,r)(h,s)=(g+(r.h), r+s).
------------------------------------------------------------------------

record FiniteFieldSymmetry (n : Nat) : Set where
  constructor fieldSymmetry
  field
    localRotation : Gauge n
    sectorRotation : C3.C3
open FiniteFieldSymmetry public

identitySymmetry : ∀ n → FiniteFieldSymmetry n
identitySymmetry n = fieldSymmetry (zeroGauge n) C3.c0

combineSymmetry :
  ∀ {n} → FiniteFieldSymmetry n → FiniteFieldSymmetry n →
  FiniteFieldSymmetry n
combineSymmetry {n} (fieldSymmetry g r) (fieldSymmetry h s) =
  fieldSymmetry (addGauge g (rotateField n r h)) (C3._∙_ r s)

actOnField :
  ∀ {n} → FiniteFieldSymmetry n → Field n → Field n
actOnField {n} (fieldSymmetry g r) f =
  translate g (rotateField n r f)

identitySymmetryActs :
  ∀ n (f : Field n) (x : Level n) →
  actOnField (identitySymmetry n) f x ≡ f x
identitySymmetryActs n f x = refl

semidirectActionComposition :
  ∀ {n} (a b : FiniteFieldSymmetry n)
  (f : Field n) (x : Level n) →
  actOnField (combineSymmetry a b) f x
  ≡ actOnField a (actOnField b f) x
semidirectActionComposition {n}
  (fieldSymmetry g r) (fieldSymmetry h s) f x =
  trans
    (cong (λ t → C3._∙_ (C3._∙_ (g x) (rotateField n r h x)) t)
      (rotateFieldComposition n r s f x))
    (C3.associative (g x) (rotateField n r h x)
      (rotateField n r (rotateField n s f) x))

------------------------------------------------------------------------
-- Coherent infinite-end evaluation: every finite-depth field gives a
-- cylinder-constant function on the INVERSE-LIMIT end set. Changing
-- its description by the pullback refinement changes no end value.
------------------------------------------------------------------------

EndPoint : Set
EndPoint = End.BalancedEndPoint

evaluateAtDepth : ∀ n → Gauge n → EndPoint → C3.C3
evaluateAtDepth n g p = g (Tower.stateAt p n)

refinedGaugeSameEndValue :
  ∀ n (g : Gauge n) (p : EndPoint) →
  evaluateAtDepth (suc n) (pullback n g) p
    ≡ evaluateAtDepth n g p
refinedGaugeSameEndValue n g p =
  cong g (Tower.coherent p n)

depthTwoAddresses : 3 * Tower.pow 3 2 ≡ 27
depthTwoAddresses = End.threeSectorDepthTwoPrefixes

depthTwoLocalRotationConfigurations :
  Tower.pow 3 (3 * Tower.pow 3 2) ≡ Tower.tetration 3 3
depthTwoLocalRotationConfigurations =
  End.ternaryConfigurationTetration

-- These results define a directed family of injective pointwise
-- homomorphisms. The global colimit and topological identification
-- with C_loc(K3,C3) still need quotient/cofinality and compactness
-- theorems on the actual infinite product topology, NOT a new axiom.
