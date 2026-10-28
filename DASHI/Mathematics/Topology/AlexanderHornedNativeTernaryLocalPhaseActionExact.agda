module DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryLocalPhaseActionExact where

------------------------------------------------------------------------
-- EXTENSION of ORIGINAL #1244 NativeTernaryFibreActionExact, not a
-- competing Map(X,C3), field group, pullback or torsor owner.
-- This module adds the C3-sector-twisted semidirect multiplication,
-- source-compatible cylinder setoid, and gauge-observation no-go.
--
-- Roots: Krasner/Kaloujnine 1950-51 permutation wreath products;
-- Alexander 1924 / Hatcher 2B.2 retain BINARY geometry ownership.
-- Johl Brown-directed, ChatGPT-assisted 2026-10-28.
-- SOURCE WRITTEN, NOT AGDA KERNEL CHECKED. No postulates or ESD edits.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact as Fibre

-- The SIGNED digit/phase chart is an explicit bijection, not type identity.
tritToPhase : Trit.Trit → C3.C3
tritToPhase Trit.neg = C3.c2
tritToPhase Trit.zero = C3.c0
tritToPhase Trit.pos = C3.c1

phaseToTrit : C3.C3 → Trit.Trit
phaseToTrit C3.c0 = Trit.zero
phaseToTrit C3.c1 = Trit.pos
phaseToTrit C3.c2 = Trit.neg

tritPhaseRoundTrip : (v : Trit.Trit) →
  phaseToTrit (tritToPhase v) ≡ v
tritPhaseRoundTrip Trit.neg = refl
tritPhaseRoundTrip Trit.zero = refl
tritPhaseRoundTrip Trit.pos = refl

phaseTritRoundTrip : (v : C3.C3) →
  tritToPhase (phaseToTrit v) ≡ v
phaseTritRoundTrip C3.c0 = refl
phaseTritRoundTrip C3.c1 = refl
phaseTritRoundTrip C3.c2 = refl

-- ORIGINAL phase owner: Fibre.FibreAction, Fibre.combine,
-- Fibre.inverseAction, Fibre.pullback, Fibre.transitiveAction,
-- Fibre.pullbackInjective and Fibre.evalLocal.
-- The external C3 left action uses PRECOMPOSITION BY INVERSE shift.
-- Fibre.rotateField is the forward precomposition; these differ in
-- orientation but agree after taking the inverse C3 generator.
inverseSectorShift : ∀ {n} → C3.C3 → End.BalancedLevel n →
  End.BalancedLevel n
inverseSectorShift shift (sector , word) =
  C3._∙_ (C3.inverse shift) sector , word

shiftField : ∀ {n} → C3.C3 → Fibre.FibreAction n →
  Fibre.FibreAction n
shiftField shift f x = f (inverseSectorShift shift x)

shiftAddressCompose : ∀ {n} (a b : C3.C3)
  (x : End.BalancedLevel n) →
  inverseSectorShift (C3._∙_ a b) x ≡
  inverseSectorShift b (inverseSectorShift a x)
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
  (f : Fibre.FibreAction n) (x : End.BalancedLevel n) →
  shiftField (C3._∙_ a b) f x ≡
  shiftField a (shiftField b f) x
shiftFieldComposeAt a b f x = cong f (shiftAddressCompose a b x)

shiftFieldAddAt : ∀ {n} (shift : C3.C3)
  (f g : Fibre.FibreAction n) (x : End.BalancedLevel n) →
  shiftField shift (Fibre.combine f g) x ≡
  Fibre.combine (shiftField shift f) (shiftField shift g) x
shiftFieldAddAt shift f g x = refl

shiftAddressProjection : ∀ n (shift : C3.C3)
  (x : End.BalancedLevel (suc n)) →
  End.balancedProjection n (inverseSectorShift shift x) ≡
  inverseSectorShift shift (End.balancedProjection n x)
shiftAddressProjection n shift (sector , word) = refl

refineRotationSquare : ∀ n (shift : C3.C3)
  (f : Fibre.FibreAction n) (x : End.BalancedLevel (suc n)) →
  Fibre.pullback n (shiftField shift f) x ≡
  shiftField shift (Fibre.pullback n f) x
refineRotationSquare n shift f x =
  cong f (sym (shiftAddressProjection n shift x))

-- Actual permutational semidirect law on existing source-owned carrier.
record TwistedPhase (n : Nat) : Set where
  constructor twistedPhase
  field
    gauge : Fibre.FibreAction n
    sector : C3.C3
open TwistedPhase public

twistedUnit : ∀ n → TwistedPhase n
twistedUnit n = twistedPhase Fibre.identityAction C3.c0

twistedMultiply : ∀ n → TwistedPhase n → TwistedPhase n →
  TwistedPhase n
twistedMultiply n a b =
  twistedPhase
    (Fibre.combine (gauge a) (shiftField (sector a) (gauge b)))
    (C3._∙_ (sector a) (sector b))

twistedAssociativeSector : ∀ n (a b c : TwistedPhase n) →
  sector (twistedMultiply n (twistedMultiply n a b) c) ≡
  sector (twistedMultiply n a (twistedMultiply n b c))
twistedAssociativeSector n a b c =
  C3.associative (sector a) (sector b) (sector c)

twistedAssociativeGaugeAt : ∀ n (a b c : TwistedPhase n)
  (x : End.BalancedLevel n) →
  gauge (twistedMultiply n (twistedMultiply n a b) c) x ≡
  gauge (twistedMultiply n a (twistedMultiply n b c)) x
twistedAssociativeGaugeAt n a b c x =
  trans
    (cong (λ z → C3._∙_
      (C3._∙_ (gauge a x) (shiftField (sector a) (gauge b) x)) z)
      (shiftFieldComposeAt (sector a) (sector b) (gauge c) x))
    (C3.associative (gauge a x)
      (shiftField (sector a) (gauge b) x)
      (shiftField (sector a) (shiftField (sector b) (gauge c)) x))

twistedLeftUnitGaugeAt : ∀ n (a : TwistedPhase n)
  (x : End.BalancedLevel n) →
  gauge (twistedMultiply n (twistedUnit n) a) x ≡ gauge a x
twistedLeftUnitGaugeAt n a x = C3.leftIdentity (gauge a x)

twistedRightUnitGaugeAt : ∀ n (a : TwistedPhase n)
  (x : End.BalancedLevel n) →
  gauge (twistedMultiply n a (twistedUnit n)) x ≡ gauge a x
twistedRightUnitGaugeAt n a x = C3.rightIdentity (gauge a x)

twistedInverse : ∀ n → TwistedPhase n → TwistedPhase n
twistedInverse n a =
  twistedPhase
    (λ x → C3.inverse
      (shiftField (C3.inverse (sector a)) (gauge a) x))
    (C3.inverse (sector a))

twistedInverseLeftGaugeAt : ∀ n (a : TwistedPhase n)
  (x : End.BalancedLevel n) →
  gauge (twistedMultiply n (twistedInverse n a) a) x ≡ C3.c0
twistedInverseLeftGaugeAt n a x =
  C3.inverseLeft (shiftField (C3.inverse (sector a)) (gauge a) x)

shiftCancel : ∀ {n} (shift : C3.C3) (x : End.BalancedLevel n) →
  inverseSectorShift (C3.inverse shift) (inverseSectorShift shift x) ≡ x
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
  (x : End.BalancedLevel n) →
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
refineTwisted n a =
  twistedPhase (Fibre.pullback n (gauge a)) (sector a)

refineTwistedGaugeHomomorphismAt : ∀ n (a b : TwistedPhase n)
  (x : End.BalancedLevel (suc n)) →
  gauge (refineTwisted n (twistedMultiply n a b)) x ≡
  gauge (twistedMultiply (suc n) (refineTwisted n a)
    (refineTwisted n b)) x
refineTwistedGaugeHomomorphismAt n a b x =
  cong (C3._∙_ (gauge a (End.balancedProjection n x)))
    (refineRotationSquare n (sector a) (gauge b) x)

-- Reuse source LocalFibreAction/evalLocal instead of second CylinderPhase.
SameOnEnds : Fibre.LocalFibreAction → Fibre.LocalFibreAction → Set
SameOnEnds a b = (end : End.BalancedEndPoint) →
  Fibre.evalLocal a end ≡ Fibre.evalLocal b end

sameOnEndsReflexive : (a : Fibre.LocalFibreAction) → SameOnEnds a a
sameOnEndsReflexive a end = refl

sameOnEndsSymmetric : (a b : Fibre.LocalFibreAction) →
  SameOnEnds a b → SameOnEnds b a
sameOnEndsSymmetric a b eq end = sym (eq end)

sameOnEndsTransitive : (a b c : Fibre.LocalFibreAction) →
  SameOnEnds a b → SameOnEnds b c → SameOnEnds a c
sameOnEndsTransitive a b c ab bc end = trans (ab end) (bc end)

sameOnEndsRefinement : ∀ n (f : Fibre.FibreAction n) →
  SameOnEnds
    (Fibre.liftLocal (suc n) (Fibre.pullback n f))
    (Fibre.liftLocal n f)
sameOnEndsRefinement n f end = Fibre.refinementEvaluation n f end

shiftEnd : C3.C3 → End.BalancedEndPoint → End.BalancedEndPoint
shiftEnd sh end = record
  { stateAt = λ n → inverseSectorShift sh (Tower.stateAt end n)
  ; coherent = λ n →
      trans
        (shiftAddressProjection n sh (Tower.stateAt end (suc n)))
        (cong (inverseSectorShift sh) (Tower.coherent end n))
  }

rotateCylinder : C3.C3 → Fibre.LocalFibreAction →
  Fibre.LocalFibreAction
rotateCylinder sh (Fibre.local-action n f) =
  Fibre.local-action n (shiftField sh f)

evalRotationSquare : ∀ n (sh : C3.C3)
  (f : Fibre.FibreAction n) (end : End.BalancedEndPoint) →
  Fibre.evalLocal (Fibre.liftLocal n (shiftField sh f)) end ≡
  Fibre.evalLocal (Fibre.liftLocal n f) (shiftEnd sh end)
evalRotationSquare n sh f end = refl

sameOnEndsRotationCongruence : (sh : C3.C3)
  (a b : Fibre.LocalFibreAction) → SameOnEnds a b →
  SameOnEnds (rotateCylinder sh a) (rotateCylinder sh b)
sameOnEndsRotationCongruence sh
  (Fibre.local-action n f) (Fibre.local-action m g) equal end =
  trans
    (evalRotationSquare n sh f end)
    (trans
      (equal (shiftEnd sh end))
      (sym (evalRotationSquare m sh g end)))

-- The ORIGINAL Fibre.difference/transitiveAction supplies transitivity.
-- Any pointwise-extensional gauge-invariant observable is constant.
gaugeInvariantObservableConstant : ∀ {n} {A : Set}
  (observable : Fibre.FibreAction n → A) →
  ((f h : Fibre.FibreAction n) →
    ((x : End.BalancedLevel n) → f x ≡ h x) →
    observable f ≡ observable h) →
  ((g f : Fibre.FibreAction n) →
    observable (Fibre.act g f) ≡ observable f) →
  (f h : Fibre.FibreAction n) → observable f ≡ observable h
gaugeInvariantObservableConstant observable respects invariant f h =
  trans
    (sym (invariant (Fibre.difference f h) f))
    (respects (Fibre.act (Fibre.difference f h) f) h
      (Fibre.transitiveAction f h))

-- Reuse original source proof, not a second function-space cardinality.
depthTwoCells : 3 * Tower.pow 3 2 ≡ 27
depthTwoCells = End.threeSectorDepthTwoPrefixes

depthTwoPhaseTableCount :
  Tower.pow 3 (3 * Tower.pow 3 2) ≡ Tower.tetration 3 3
depthTwoPhaseTableCount = End.ternaryConfigurationTetration

-- No quotient type, no continuity=>finite-depth factor proof, no geometry.
