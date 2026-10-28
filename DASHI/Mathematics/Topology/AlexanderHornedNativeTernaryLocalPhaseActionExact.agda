module DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryLocalPhaseActionExact where

------------------------------------------------------------------------
-- Finite local phase action over the ORIGINAL native ternary end tower.
-- Reuses #1244 BalancedLevel, balancedProjection, and C3 group operations.
--
-- Earlier mathematical owners: pointwise finite groups, semidirect and
-- permutational wreath products (Kaloujnine/Krasner 1950-51);
-- Alexander 1924, Hatcher's original BINARY horn address source.
-- Repository integration: Johl Brown-directed / ChatGPT 2026-10-28.
-- This is NOT the topological exterior group or a Monster/Spin lift.
-- SOURCE-WRITTEN, not an Agda kernel receipt; no postulates or funext.
-- Function identities are POINTWISE rather than unproved function eq.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as Native
import DASHI.Cognition.RecursiveFibreTower as Tower

Address : Nat → Set
Address = Native.BalancedLevel

LocalPhase : Nat → Set
LocalPhase n = Address n → C3.C3

phaseZero : ∀ {n} → LocalPhase n
phaseZero x = C3.c0

phaseAdd : ∀ {n} → LocalPhase n → LocalPhase n → LocalPhase n
phaseAdd f g x = C3._∙_ (f x) (g x)

phaseNeg : ∀ {n} → LocalPhase n → LocalPhase n
phaseNeg f x = C3.inverse (f x)

phaseAssociativeAt : ∀ {n} (f g h : LocalPhase n) (x : Address n) →
  phaseAdd (phaseAdd f g) h x ≡ phaseAdd f (phaseAdd g h) x
phaseAssociativeAt f g h x = C3.associative (f x) (g x) (h x)

phaseLeftUnitAt : ∀ {n} (f : LocalPhase n) (x : Address n) →
  phaseAdd phaseZero f x ≡ f x
phaseLeftUnitAt f x = C3.leftIdentity (f x)

phaseRightUnitAt : ∀ {n} (f : LocalPhase n) (x : Address n) →
  phaseAdd f phaseZero x ≡ f x
phaseRightUnitAt f x = C3.rightIdentity (f x)

phaseInverseLeftAt : ∀ {n} (f : LocalPhase n) (x : Address n) →
  phaseAdd (phaseNeg f) f x ≡ C3.c0
phaseInverseLeftAt f x = C3.inverseLeft (f x)

phaseInverseRightAt : ∀ {n} (f : LocalPhase n) (x : Address n) →
  phaseAdd f (phaseNeg f) x ≡ C3.c0
phaseInverseRightAt f x = C3.inverseRight (f x)

-- Local gauge translations really act on fields at each source address.
translate : ∀ {n} → LocalPhase n → LocalPhase n → LocalPhase n
translate g f = phaseAdd g f

translateAssociativeAt : ∀ {n} (g h f : LocalPhase n)
  (x : Address n) →
  translate (phaseAdd g h) f x ≡ translate g (translate h f) x
translateAssociativeAt g h f x = C3.associative (g x) (h x) (f x)

-- The canonical refinement is pullback along source-owned projection.
refine : (n : Nat) → LocalPhase n → LocalPhase (suc n)
refine n f x = f (Native.balancedProjection n x)

refineHomomorphismAt : ∀ n (f g : LocalPhase n)
  (x : Address (suc n)) →
  refine n (phaseAdd f g) x ≡
    phaseAdd (refine n f) (refine n g) x
refineHomomorphismAt n f g x = refl

refineInverseAt : ∀ n (f : LocalPhase n)
  (x : Address (suc n)) →
  refine n (phaseNeg f) x ≡ phaseNeg (refine n f) x
refineInverseAt n f x = refl

refineTranslationAt : ∀ n (g f : LocalPhase n)
  (x : Address (suc n)) →
  refine n (translate g f) x ≡
  translate (refine n g) (refine n f) x
refineTranslationAt n g f x = refl

-- Explicit right section exists: append a fixed valid trit.
child : (n : Nat) → Address n → Address (suc n)
child n (sector , prefix) = sector , Native.snoc prefix Trit.neg

childSection : ∀ n (x : Address n) →
  Native.balancedProjection n (child n x) ≡ x
childSection n (sector , prefix) =
  cong (λ suffix → (sector , suffix))
    (Native.dropLastSnoc prefix Trit.neg)

refineReflectsEquality : ∀ n (f g : LocalPhase n) →
  ((x : Address (suc n)) → refine n f x ≡ refine n g x) →
  (x : Address n) → f x ≡ g x
refineReflectsEquality n f g equal x =
  trans (sym (cong f (childSection n x)))
    (trans (equal (child n x)) (cong g (childSection n x)))

-- Inverse of the ACTUAL external sector rotation; internal trits fixed.
shiftAddress : ∀ {n} → C3.C3 → Address n → Address n
shiftAddress a (sector , word) =
  C3._∙_ (C3.inverse a) sector , word

shiftField : ∀ {n} → C3.C3 → LocalPhase n → LocalPhase n
shiftField a f x = f (shiftAddress a x)

shiftAddressCompose : ∀ {n} (a b : C3.C3) (x : Address n) →
  shiftAddress (C3._∙_ a b) x ≡ shiftAddress b (shiftAddress a x)
shiftAddressCompose C3.c0 C3.c0 (C3.c0 , word) = refl
shiftAddressCompose C3.c0 C3.c0 (C3.c1 , word) = refl
shiftAddressCompose C3.c0 C3.c0 (C3.c2 , word) = refl
shiftAddressCompose C3.c0 C3.c1 (C3.c0 , word) = refl
shiftAddressCompose C3.c0 C3.c1 (C3.c1 , word) = refl
shiftAddressCompose C3.c0 C3.c1 (C3.c2 , word) = refl
shiftAddressCompose C3.c0 C3.c2 (C3.c0 , word) = refl
shiftAddressCompose C3.c0 C3.c2 (C3.c1 , word) = refl
shiftAddressCompose C3.c0 C3.c2 (C3.c2 , word) = refl
shiftAddressCompose C3.c1 C3.c0 (C3.c0 , word) = refl
shiftAddressCompose C3.c1 C3.c0 (C3.c1 , word) = refl
shiftAddressCompose C3.c1 C3.c0 (C3.c2 , word) = refl
shiftAddressCompose C3.c1 C3.c1 (C3.c0 , word) = refl
shiftAddressCompose C3.c1 C3.c1 (C3.c1 , word) = refl
shiftAddressCompose C3.c1 C3.c1 (C3.c2 , word) = refl
shiftAddressCompose C3.c1 C3.c2 (C3.c0 , word) = refl
shiftAddressCompose C3.c1 C3.c2 (C3.c1 , word) = refl
shiftAddressCompose C3.c1 C3.c2 (C3.c2 , word) = refl
shiftAddressCompose C3.c2 C3.c0 (C3.c0 , word) = refl
shiftAddressCompose C3.c2 C3.c0 (C3.c1 , word) = refl
shiftAddressCompose C3.c2 C3.c0 (C3.c2 , word) = refl
shiftAddressCompose C3.c2 C3.c1 (C3.c0 , word) = refl
shiftAddressCompose C3.c2 C3.c1 (C3.c1 , word) = refl
shiftAddressCompose C3.c2 C3.c1 (C3.c2 , word) = refl
shiftAddressCompose C3.c2 C3.c2 (C3.c0 , word) = refl
shiftAddressCompose C3.c2 C3.c2 (C3.c1 , word) = refl
shiftAddressCompose C3.c2 C3.c2 (C3.c2 , word) = refl

shiftFieldComposeAt : ∀ {n} (a b : C3.C3)
  (f : LocalPhase n) (x : Address n) →
  shiftField (C3._∙_ a b) f x ≡ shiftField a (shiftField b f) x
shiftFieldComposeAt a b f x = cong f (shiftAddressCompose a b x)

shiftFieldAddAt : ∀ {n} (a : C3.C3) (f g : LocalPhase n)
  (x : Address n) →
  shiftField a (phaseAdd f g) x ≡
  phaseAdd (shiftField a f) (shiftField a g) x
shiftFieldAddAt a f g x = refl

shiftAddressProjection : ∀ n (a : C3.C3)
  (x : Address (suc n)) →
  Native.balancedProjection n (shiftAddress a x) ≡
  shiftAddress a (Native.balancedProjection n x)
shiftAddressProjection n a (sector , prefix) = refl

refineRotationSquare : ∀ n (a : C3.C3)
  (f : LocalPhase n) (x : Address (suc n)) →
  refine n (shiftField a f) x ≡ shiftField a (refine n f) x
refineRotationSquare n a f x =
  cong f (sym (shiftAddressProjection n a x))

record TwistedPhase (n : Nat) : Set where
  constructor twistedPhase
  field
    gauge : LocalPhase n
    sector : C3.C3
open TwistedPhase public

twistedUnit : ∀ n → TwistedPhase n
twistedUnit n = twistedPhase phaseZero C3.c0

twistedMultiply : ∀ n → TwistedPhase n → TwistedPhase n →
  TwistedPhase n
twistedMultiply n a b =
  twistedPhase
    (phaseAdd (gauge a) (shiftField (sector a) (gauge b)))
    (C3._∙_ (sector a) (sector b))

twistedAssociativeSector : ∀ n (a b c : TwistedPhase n) →
  sector (twistedMultiply n (twistedMultiply n a b) c) ≡
  sector (twistedMultiply n a (twistedMultiply n b c))
twistedAssociativeSector n a b c =
  C3.associative (sector a) (sector b) (sector c)

twistedAssociativeGaugeAt : ∀ n (a b c : TwistedPhase n)
  (x : Address n) →
  gauge (twistedMultiply n (twistedMultiply n a b) c) x ≡
  gauge (twistedMultiply n a (twistedMultiply n b c)) x
twistedAssociativeGaugeAt n a b c x =
  trans
    (cong (λ z →
      C3._∙_
        (C3._∙_ (gauge a x) (shiftField (sector a) (gauge b) x)) z)
      (shiftFieldComposeAt (sector a) (sector b) (gauge c) x))
    (C3.associative (gauge a x)
      (shiftField (sector a) (gauge b) x)
      (shiftField (sector a) (shiftField (sector b) (gauge c)) x))

twistedLeftUnitGaugeAt : ∀ n (a : TwistedPhase n)
  (x : Address n) →
  gauge (twistedMultiply n (twistedUnit n) a) x ≡ gauge a x
twistedLeftUnitGaugeAt n a x = C3.leftIdentity (gauge a x)

twistedRightUnitGaugeAt : ∀ n (a : TwistedPhase n)
  (x : Address n) →
  gauge (twistedMultiply n a (twistedUnit n)) x ≡ gauge a x
twistedRightUnitGaugeAt n a x = C3.rightIdentity (gauge a x)

twistedInverse : ∀ n → TwistedPhase n → TwistedPhase n
twistedInverse n a =
  twistedPhase
    (λ x → C3.inverse
      (shiftField (C3.inverse (sector a)) (gauge a) x))
    (C3.inverse (sector a))

twistedInverseLeftGaugeAt : ∀ n (a : TwistedPhase n)
  (x : Address n) →
  gauge (twistedMultiply n (twistedInverse n a) a) x ≡ C3.c0
twistedInverseLeftGaugeAt n a x =
  C3.inverseLeft (shiftField (C3.inverse (sector a)) (gauge a) x)

shiftCancel : ∀ {n} (a : C3.C3) (x : Address n) →
  shiftAddress (C3.inverse a) (shiftAddress a x) ≡ x
shiftCancel C3.c0 (C3.c0 , word) = refl
shiftCancel C3.c0 (C3.c1 , word) = refl
shiftCancel C3.c0 (C3.c2 , word) = refl
shiftCancel C3.c1 (C3.c0 , word) = refl
shiftCancel C3.c1 (C3.c1 , word) = refl
shiftCancel C3.c1 (C3.c2 , word) = refl
shiftCancel C3.c2 (C3.c0 , word) = refl
shiftCancel C3.c2 (C3.c1 , word) = refl
shiftCancel C3.c2 (C3.c2 , word) = refl

twistedInverseRightGaugeAt : ∀ n (a : TwistedPhase n)
  (x : Address n) →
  gauge (twistedMultiply n a (twistedInverse n a)) x ≡ C3.c0
twistedInverseRightGaugeAt n a x =
  trans
    (cong (λ z → C3._∙_ (gauge a x) (C3.inverse z))
      (cong (gauge a) (shiftCancel (sector a) x)))
    (C3.inverseRight (gauge a x))

twistedInverseLeftSector : ∀ n (a : TwistedPhase n) →
  sector (twistedMultiply n (twistedInverse n a) a) ≡ C3.c0
twistedInverseLeftSector n a = C3.inverseLeft (sector a)

twistedInverseRightSector : ∀ n (a : TwistedPhase n) →
  sector (twistedMultiply n a (twistedInverse n a)) ≡ C3.c0
twistedInverseRightSector n a = C3.inverseRight (sector a)

refineTwisted : ∀ n → TwistedPhase n → TwistedPhase (suc n)
refineTwisted n a = twistedPhase (refine n (gauge a)) (sector a)

refineTwistedGaugeHomomorphismAt : ∀ n (a b : TwistedPhase n)
  (x : Address (suc n)) →
  gauge (refineTwisted n (twistedMultiply n a b)) x ≡
  gauge (twistedMultiply (suc n) (refineTwisted n a)
    (refineTwisted n b)) x
refineTwistedGaugeHomomorphismAt n a b x =
  cong (C3._∙_ (gauge a (Native.balancedProjection n x)))
    (refineRotationSquare n (sector a) (gauge b) x)

-- Finite cylinder functions evaluated on the ACTUAL inverse limit.
-- No compactness, topology or universal continuous-function theorem here.
record CylinderPhase : Set where
  constructor cylinderPhase
  field
    depth : Nat
    phase : LocalPhase depth
open CylinderPhase public

valueAtEnd : CylinderPhase → Native.BalancedEndPoint → C3.C3
valueAtEnd (cylinderPhase n f) x = f (Tower.stateAt x n)

refinementPreservesEndValue : ∀ n (f : LocalPhase n)
  (x : Native.BalancedEndPoint) →
  valueAtEnd (cylinderPhase (suc n) (refine n f)) x ≡
  valueAtEnd (cylinderPhase n f) x
refinementPreservesEndValue n f x = cong f (Tower.coherent x n)

shiftEnd : C3.C3 → Native.BalancedEndPoint →
  Native.BalancedEndPoint
shiftEnd a x = record
  { stateAt = λ n → shiftAddress a (Tower.stateAt x n)
  ; coherent = λ n →
      trans
        (shiftAddressProjection n a (Tower.stateAt x (suc n)))
        (cong (shiftAddress a) (Tower.coherent x n))
  }

endRotationValueSquare : ∀ n (a : C3.C3)
  (f : LocalPhase n) (x : Native.BalancedEndPoint) →
  valueAtEnd (cylinderPhase n (shiftField a f)) x ≡
  valueAtEnd (cylinderPhase n f) (shiftEnd a x)
endRotationValueSquare n a f x = refl

-- Reuse source-owned numerical identity, not a new cardinality ontology.
depthTwoCells : 3 * Tower.pow 3 2 ≡ 27
depthTwoCells = Native.threeSectorDepthTwoPrefixes

depthTwoLocalPhaseCount :
  Tower.pow 3 (3 * Tower.pow 3 2) ≡ Tower.tetration 3 3
depthTwoLocalPhaseCount = Native.ternaryConfigurationTetration
