module DASHI.Mathematics.Topology.AlexanderHornedNativeTernarySemidirectActionExact where

------------------------------------------------------------------------
-- REUSE-FIRST SEMIDIRECT FIELD-ACTION / REFINEMENT ADAPTER.
--
-- ORIGINAL OWNERS (both already on PR #1244):
-- * NativeTernaryFibreActionExact: Map(K_n,C3) group, local torsor,
--   injective pullback and coherent end evaluation.
-- * NativeTernaryLocalPhaseActionExact: correct inverse-sector twist,
--   semidirect multiplication, both inverses, associativity,
--   end-cylinder relation and rotation-preserving refinement.
--
-- THIS source adds only the action of that already-defined group
-- on phase fields, a proof that multiplication agrees with sequential
-- action, and faithful equivariant refinement of that action. No new
-- competing group laws, no function extensionality or postulates.
--
-- The original horned exterior π1, Monster 3B and SU2 holonomy
-- remain separate. Historical group-theory and source author credits
-- belong to original math and earlier named DASHI owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact as Fibre
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryLocalPhaseActionExact as Owner

Gauge : Nat → Set
Gauge = Fibre.FibreAction

Field : Nat → Set
Field = Fibre.PhaseField

FieldSymmetry : Nat → Set
FieldSymmetry = Owner.TwistedPhase

fieldSymmetry : ∀ {n} → Gauge n → C3.C3 → FieldSymmetry n
fieldSymmetry = Owner.twistedPhase

localRotation : ∀ {n} → FieldSymmetry n → Gauge n
localRotation = Owner.gauge

sectorRotation : ∀ {n} → FieldSymmetry n → C3.C3
sectorRotation = Owner.sector

zeroGauge : ∀ n → Gauge n
zeroGauge n = Fibre.identityAction

addGauge : ∀ {n} → Gauge n → Gauge n → Gauge n
addGauge = Fibre.combine

sectorAction : ∀ n → C3.C3 → Gauge n → Gauge n
sectorAction n r f = Owner.shiftField r f

combineSymmetry :
  ∀ {n} → FieldSymmetry n → FieldSymmetry n →
  FieldSymmetry n
combineSymmetry {n} = Owner.twistedMultiply n

identitySymmetry : ∀ n → FieldSymmetry n
identitySymmetry = Owner.twistedUnit

inverseSymmetry : ∀ {n} → FieldSymmetry n → FieldSymmetry n
inverseSymmetry {n} = Owner.twistedInverse n

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

sectorActionComposition :
  ∀ n (r s : C3.C3) (g : Gauge n)
  (x : End.BalancedLevel n) →
  sectorAction n (C3._∙_ r s) g x
    ≡ sectorAction n r (sectorAction n s g) x
sectorActionComposition n r s g x =
  Owner.shiftFieldComposeAt r s g x

sectorActionPullbackSquare :
  ∀ n (r : C3.C3) (g : Gauge n)
  (x : End.BalancedLevel (suc n)) →
  Fibre.pullback n (sectorAction n r g) x
    ≡ sectorAction (suc n) r (Fibre.pullback n g) x
sectorActionPullbackSquare n r g x =
  Owner.refineRotationSquare n r g x

actOnField : ∀ {n} → FieldSymmetry n → Field n → Field n
actOnField a f =
  Fibre.act (localRotation a) (Owner.shiftField (sectorRotation a) f)

identityActs :
  ∀ n (f : Field n) (x : End.BalancedLevel n) →
  actOnField (identitySymmetry n) f x ≡ f x
identityActs n f x = refl

semidirectActionComposition :
  ∀ {n} (a b : FieldSymmetry n)
  (f : Field n) (x : End.BalancedLevel n) →
  actOnField (combineSymmetry a b) f x
    ≡ actOnField a (actOnField b f) x
semidirectActionComposition {n} a b f x =
  trans
    (cong
      (λ z → C3._∙_
        (C3._∙_ (localRotation a x)
          (Owner.shiftField (sectorRotation a) (localRotation b) x))
        z)
      (Owner.shiftFieldComposeAt
        (sectorRotation a) (sectorRotation b) f x))
    (trans
      (C3.associative
        (localRotation a x)
        (Owner.shiftField (sectorRotation a) (localRotation b) x)
        (Owner.shiftField (sectorRotation a)
          (Owner.shiftField (sectorRotation b) f) x))
      (cong
        (λ z → C3._∙_ (localRotation a x) z)
        (sym (Owner.shiftFieldAddAt
          (sectorRotation a)
          (localRotation b)
          (Owner.shiftField (sectorRotation b) f) x))))

semidirectGaugeAssociativity :
  ∀ {n} (a b c : FieldSymmetry n)
  (x : End.BalancedLevel n) →
  localRotation (combineSymmetry (combineSymmetry a b) c) x
    ≡ localRotation (combineSymmetry a (combineSymmetry b c)) x
semidirectGaugeAssociativity {n} a b c x =
  Owner.twistedAssociativeGaugeAt n a b c x

semidirectSectorAssociativity :
  ∀ {n} (a b c : FieldSymmetry n) →
  sectorRotation (combineSymmetry (combineSymmetry a b) c)
    ≡ sectorRotation (combineSymmetry a (combineSymmetry b c))
semidirectSectorAssociativity {n} a b c =
  Owner.twistedAssociativeSector n a b c

semidirectLeftInverseGauge :
  ∀ {n} (a : FieldSymmetry n) (x : End.BalancedLevel n) →
  localRotation (combineSymmetry (inverseSymmetry a) a) x ≡ C3.c0
semidirectLeftInverseGauge {n} a x =
  Owner.twistedInverseLeftGaugeAt n a x

semidirectRightInverseGauge :
  ∀ {n} (a : FieldSymmetry n) (x : End.BalancedLevel n) →
  localRotation (combineSymmetry a (inverseSymmetry a)) x ≡ C3.c0
semidirectRightInverseGauge {n} a x =
  Owner.twistedInverseRightGaugeAt n a x

refineSymmetry :
  ∀ n → FieldSymmetry n → FieldSymmetry (suc n)
refineSymmetry = Owner.refineTwisted

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
refineSymmetryPreservesMultiplication n a b x =
  Owner.refineTwistedGaugeHomomorphismAt n a b x

refineSymmetryPreservesAction :
  ∀ n (a : FieldSymmetry n) (f : Field n)
  (x : End.BalancedLevel (suc n)) →
  Fibre.pullback n (actOnField a f) x
    ≡ actOnField (refineSymmetry n a) (Fibre.pullback n f) x
refineSymmetryPreservesAction n a f x =
  trans
    (Fibre.pullbackMultiplication n (localRotation a)
      (Owner.shiftField (sectorRotation a) f) x)
    (cong
      (λ v → C3._∙_ (Fibre.pullback n (localRotation a) x) v)
      (Owner.refineRotationSquare n (sectorRotation a) f x))

refineSymmetryFaithful :
  ∀ n (a b : FieldSymmetry n) →
  ((x : End.BalancedLevel (suc n)) →
    localRotation (refineSymmetry n a) x
    ≡ localRotation (refineSymmetry n b) x) →
  sectorRotation (refineSymmetry n a)
    ≡ sectorRotation (refineSymmetry n b) →
  ((x : End.BalancedLevel n) →
    localRotation a x ≡ localRotation b x)
refineSymmetryFaithful n a b sameGauges sameSectors =
  Fibre.pullbackInjective n (localRotation a) (localRotation b)
    sameGauges

-- The original owner also proves a strong cylinder-setoid congruence
-- under sector rotation and gauge-invariant observer triviality.
-- No second such record/type is created here.
