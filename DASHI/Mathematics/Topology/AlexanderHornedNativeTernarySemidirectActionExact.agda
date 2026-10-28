module DASHI.Mathematics.Topology.AlexanderHornedNativeTernarySemidirectActionExact where

------------------------------------------------------------------------
-- NEW OWNER EXTENSION: NATIVE TERNARY FIBRE SEMIDIRECT ACTION.
--
-- REUSE, DO NOT DUPLICATE:
-- AlexanderHornedNativeTernaryFibreActionExact already constructs the
-- C3^X local group, its free/transitive field action, injective
-- refinement pullbacks and coherent infinite-end evaluation.
--
-- This extension adds the INVERSE-PULLBACK sector action of C3,
-- the finite semidirect product, multiplication/action composition,
-- and compatibility with the already owned injective pullbacks.
--
-- |X_n|=3^(n+1), |Map(X_n,C3)|=3^(3^(n+1)),
-- |Map(X_n,C3) ⋊ C3|=3^(3^(n+1)+1).
-- At n=2 the local subgroup has 3^27 elements. This is a
-- group of END-FIBRE transformations, NOT the horned-exterior
-- orbifold fundamental group or a physical gauge holonomy.
--
-- Attribution: classical permutational wreath products; Hatcher's
-- binary geometry owned by #1244; actual original group and field
-- source proofs reused, not reassigned. Agda kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact as Native

Gauge : Nat → Set
Gauge = Native.FibreAction

Field : Nat → Set
Field = Native.PhaseField

addGauge : ∀ {n} → Gauge n → Gauge n → Gauge n
addGauge = Native.combine

zeroGauge : ∀ n → Gauge n
zeroGauge n = Native.identityAction

commutativeC3 : ∀ a b → C3._∙_ a b ≡ C3._∙_ b a
commutativeC3 C3.c0 C3.c0 = refl
commutativeC3 C3.c0 C3.c1 = refl
commutativeC3 C3.c0 C3.c2 = refl
commutativeC3 C3.c1 C3.c0 = refl
commutativeC3 C3.c1 C3.c1 = refl
commutativeC3 C3.c1 C3.c2 = refl
commutativeC3 C3.c2 C3.c0 = refl
commutativeC3 C3.c2 C3.c1 = refl
commutativeC3 C3.c2 C3.c2 = refl

-- Earlier owner chooses FORWARD pullback rotation (precomposition).
-- Left group action on fields MUST use inverse pullback. Thus sector
-- c1 acts by the square of the existing forward rotation.
sectorAction : ∀ n → C3.C3 → Gauge n → Gauge n
sectorAction n C3.c0 f = f
sectorAction n C3.c1 f =
  Native.rotateField n (Native.rotateField n f)
sectorAction n C3.c2 f = Native.rotateField n f

sectorActionIdentity :
  ∀ n (f : Gauge n) (x : End.BalancedLevel n) →
  sectorAction n C3.c0 f x ≡ f x
sectorActionIdentity n f x = refl

sectorActionComposition :
  ∀ n (r s : C3.C3) (f : Gauge n) (x : End.BalancedLevel n) →
  sectorAction n (C3._∙_ r s) f x
    ≡ sectorAction n r (sectorAction n s f) x
sectorActionComposition n C3.c0 s f x = refl
sectorActionComposition n C3.c1 C3.c0 f x = refl
sectorActionComposition n C3.c1 C3.c1 f x =
  sym (Native.rotateFieldCubed n (Native.rotateField n f) x)
sectorActionComposition n C3.c1 C3.c2 f x =
  sym (Native.rotateFieldCubed n f x)
sectorActionComposition n C3.c2 C3.c0 f x = refl
sectorActionComposition n C3.c2 C3.c1 f x =
  sym (Native.rotateFieldCubed n f x)
sectorActionComposition n C3.c2 C3.c2 f x = refl

sectorActionDistributes :
  ∀ n (r : C3.C3) (g h : Gauge n)
  (x : End.BalancedLevel n) →
  sectorAction n r (addGauge g h) x
    ≡ addGauge (sectorAction n r g) (sectorAction n r h) x
sectorActionDistributes n C3.c0 g h x = refl
sectorActionDistributes n C3.c1 g h x = refl
sectorActionDistributes n C3.c2 g h x = refl

sectorActionPreservesZero :
  ∀ n (r : C3.C3) (x : End.BalancedLevel n) →
  sectorAction n r (zeroGauge n) x ≡ C3.c0
sectorActionPreservesZero n C3.c0 x = refl
sectorActionPreservesZero n C3.c1 x = refl
sectorActionPreservesZero n C3.c2 x = refl

sectorActionPreservesInverse :
  ∀ n (r : C3.C3) (g : Gauge n)
  (x : End.BalancedLevel n) →
  sectorAction n r (Native.inverseAction g) x
    ≡ C3.inverse (sectorAction n r g x)
sectorActionPreservesInverse n C3.c0 g x = refl
sectorActionPreservesInverse n C3.c1 g x = refl
sectorActionPreservesInverse n C3.c2 g x = refl

sectorActionPullbackSquare :
  ∀ n (r : C3.C3) (g : Gauge n)
  (x : End.BalancedLevel (suc n)) →
  Native.pullback n (sectorAction n r g) x
    ≡ sectorAction (suc n) r (Native.pullback n g) x
sectorActionPullbackSquare n C3.c0 g x = refl
sectorActionPullbackSquare n C3.c1 g x =
  trans
    (sym (Native.rotatePullbackSquare n (Native.rotateField n g) x))
    (sym (Native.rotatePullbackSquare n g
      (End.rotateBalancedLevel (suc n) x)))
sectorActionPullbackSquare n C3.c2 g x =
  sym (Native.rotatePullbackSquare n g x)

record FieldSymmetry (n : Nat) : Set where
  constructor fieldSymmetry
  field
    localRotation : Gauge n
    sectorRotation : C3.C3
open FieldSymmetry public

identitySymmetry : ∀ n → FieldSymmetry n
identitySymmetry n = fieldSymmetry (zeroGauge n) C3.c0

combineSymmetry :
  ∀ {n} → FieldSymmetry n → FieldSymmetry n →
  FieldSymmetry n
combineSymmetry {n} (fieldSymmetry g r) (fieldSymmetry h s) =
  fieldSymmetry
    (addGauge g (sectorAction n r h))
    (C3._∙_ r s)

actOnField : ∀ {n} → FieldSymmetry n → Field n → Field n
actOnField {n} (fieldSymmetry g r) f =
  Native.act g (sectorAction n r f)

identityActs :
  ∀ n (f : Field n) (x : End.BalancedLevel n) →
  actOnField (identitySymmetry n) f x ≡ f x
identityActs n f x = refl

semidirectActionComposition :
  ∀ {n} (a b : FieldSymmetry n)
  (f : Field n) (x : End.BalancedLevel n) →
  actOnField (combineSymmetry a b) f x
    ≡ actOnField a (actOnField b f) x
semidirectActionComposition {n}
  (fieldSymmetry g r) (fieldSymmetry h s) f x =
  trans
    (cong
      (λ t → C3._∙_ (C3._∙_ (g x) (sectorAction n r h x)) t)
      (sectorActionComposition n r s f x))
    (trans
      (C3.associative
        (g x) (sectorAction n r h x)
        (sectorAction n r (sectorAction n s f) x))
      (cong (λ t → C3._∙_ (g x) t)
        (sym (sectorActionDistributes n r h
          (sectorAction n s f) x))))

sectorProjectionPreservesProduct :
  ∀ {n} (a b : FieldSymmetry n) →
  sectorRotation (combineSymmetry a b)
    ≡ C3._∙_ (sectorRotation a) (sectorRotation b)
sectorProjectionPreservesProduct a b = refl

-- The twisted group operation is associative pointwise on its function
-- component; no function extensionality axiom is needed.
semidirectGaugeAssociativity :
  ∀ {n} (a b c : FieldSymmetry n)
  (x : End.BalancedLevel n) →
  localRotation (combineSymmetry (combineSymmetry a b) c) x
    ≡ localRotation (combineSymmetry a (combineSymmetry b c)) x
semidirectGaugeAssociativity {n}
  (fieldSymmetry g r) (fieldSymmetry h s)
  (fieldSymmetry k t) x =
  trans
    (C3.associative (g x) (sectorAction n r h x)
      (sectorAction n (C3._∙_ r s) k x))
    (trans
      (cong
        (λ z → C3._∙_ (g x) (C3._∙_ (sectorAction n r h x) z))
        (sectorActionComposition n r s k x))
      (cong (λ t → C3._∙_ (g x) t)
        (sym (sectorActionDistributes n r h
          (sectorAction n s k) x))))

semidirectSectorAssociativity :
  ∀ {n} (a b c : FieldSymmetry n) →
  sectorRotation (combineSymmetry (combineSymmetry a b) c)
    ≡ sectorRotation (combineSymmetry a (combineSymmetry b c))
semidirectSectorAssociativity a b c =
  C3.associative (sectorRotation a) (sectorRotation b) (sectorRotation c)


------------------------------------------------------------------------
-- Refine the WHOLE semidirect actor along the established injective
-- fibre-group pullback while keeping the external sector unchanged.
------------------------------------------------------------------------

refineSymmetry :
  ∀ n → FieldSymmetry n → FieldSymmetry (suc n)
refineSymmetry n (fieldSymmetry g r) =
  fieldSymmetry (Native.pullback n g) r

refineSymmetrySectorUnchanged :
  ∀ n (a : FieldSymmetry n) →
  sectorRotation (refineSymmetry n a) ≡ sectorRotation a
refineSymmetrySectorUnchanged n a = refl

refineSymmetryPreservesMultiplication :
  ∀ n (a b : FieldSymmetry n)
  (x : End.BalancedLevel (suc n)) →
  localRotation (refineSymmetry n (combineSymmetry a b)) x
  ≡ localRotation
       (combineSymmetry (refineSymmetry n a)
                        (refineSymmetry n b)) x
refineSymmetryPreservesMultiplication n
  (fieldSymmetry g r) (fieldSymmetry h s) x =
  trans
    (Native.pullbackMultiplication n g (sectorAction n r h) x)
    (cong
      (λ t → C3._∙_ (Native.pullback n g x) t)
      (sectorActionPullbackSquare n r h x))

refineSymmetryPreservesAction :
  ∀ n (a : FieldSymmetry n) (f : Field n)
  (x : End.BalancedLevel (suc n)) →
  Native.pullback n (actOnField a f) x
  ≡ actOnField (refineSymmetry n a) (Native.pullback n f) x
refineSymmetryPreservesAction n (fieldSymmetry g r) f x =
  trans
    (Native.pullbackMultiplication n g (sectorAction n r f) x)
    (cong
      (λ t → C3._∙_ (Native.pullback n g x) t)
      (sectorActionPullbackSquare n r f x))

refineSymmetryFaithful :
  ∀ n (a b : FieldSymmetry n) →
  ((x : End.BalancedLevel (suc n)) →
    localRotation (refineSymmetry n a) x
    ≡ localRotation (refineSymmetry n b) x) →
  sectorRotation (refineSymmetry n a)
    ≡ sectorRotation (refineSymmetry n b) →
  ((x : End.BalancedLevel n) →
    localRotation a x ≡ localRotation b x)
refineSymmetryFaithful n a b pointwiseEqual sectorEqual =
  Native.pullbackInjective n (localRotation a) (localRotation b)
    pointwiseEqual


------------------------------------------------------------------------
-- CLOSE THE FINITE SEMIDIRECT GROUP LAWS POINTWISE.
-- Source owner supplies the C3 inverse on gauge values. The external
-- C3 inverse additionally moves the ADDRESS before sign inversion.
------------------------------------------------------------------------

inverseSymmetry :
  ∀ {n} → FieldSymmetry n → FieldSymmetry n
inverseSymmetry {n} (fieldSymmetry g r) =
  fieldSymmetry
    (Native.inverseAction (sectorAction n (C3.inverse r) g))
    (C3.inverse r)

sectorActionCancelsItsInverse :
  ∀ n (r : C3.C3) (g : Gauge n)
  (x : End.BalancedLevel n) →
  sectorAction n r (sectorAction n (C3.inverse r) g) x ≡ g x
sectorActionCancelsItsInverse n C3.c0 g x = refl
sectorActionCancelsItsInverse n C3.c1 g x =
  Native.rotateFieldCubed n g x
sectorActionCancelsItsInverse n C3.c2 g x =
  Native.rotateFieldCubed n g x

semidirectRightInverseGauge :
  ∀ {n} (a : FieldSymmetry n) (x : End.BalancedLevel n) →
  localRotation (combineSymmetry a (inverseSymmetry a)) x ≡ C3.c0
semidirectRightInverseGauge {n} (fieldSymmetry g r) x =
  trans
    (cong (λ t → C3._∙_ (g x) t)
      (sectorActionPreservesInverse n r
        (sectorAction n (C3.inverse r) g) x))
    (trans
      (cong (λ value → C3._∙_ (g x) (C3.inverse value))
        (sectorActionCancelsItsInverse n r g x))
      (C3.inverseRight (g x)))

semidirectRightInverseSector :
  ∀ {n} (a : FieldSymmetry n) →
  sectorRotation (combineSymmetry a (inverseSymmetry a)) ≡ C3.c0
semidirectRightInverseSector (fieldSymmetry g r) =
  C3.inverseRight r

semidirectLeftInverseGauge :
  ∀ {n} (a : FieldSymmetry n) (x : End.BalancedLevel n) →
  localRotation (combineSymmetry (inverseSymmetry a) a) x ≡ C3.c0
semidirectLeftInverseGauge {n} (fieldSymmetry g r) x =
  C3.inverseLeft (sectorAction n (C3.inverse r) g x)

semidirectLeftInverseSector :
  ∀ {n} (a : FieldSymmetry n) →
  sectorRotation (combineSymmetry (inverseSymmetry a) a) ≡ C3.c0
semidirectLeftInverseSector (fieldSymmetry g r) =
  C3.inverseLeft r

semidirectLeftIdentityGauge :
  ∀ {n} (a : FieldSymmetry n) (x : End.BalancedLevel n) →
  localRotation (combineSymmetry (identitySymmetry n) a) x
    ≡ localRotation a x
semidirectLeftIdentityGauge a x = refl

semidirectRightIdentityGauge :
  ∀ {n} (a : FieldSymmetry n) (x : End.BalancedLevel n) →
  localRotation (combineSymmetry a (identitySymmetry n)) x
    ≡ localRotation a x
semidirectRightIdentityGauge {n} a x =
  trans
    (cong (λ t → C3._∙_ (localRotation a x) t)
      (sectorActionPreservesZero n (sectorRotation a) x))
    (C3.rightIdentity (localRotation a x))

-- These named operations are on finite-depth C3 fields; their direct
-- limit equals the locally constant continuous group only after an
-- independent compact-clopen factorization/colimit proof.
