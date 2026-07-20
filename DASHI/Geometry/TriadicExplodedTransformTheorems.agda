module DASHI.Geometry.TriadicExplodedTransformTheorems where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Geometry.TriadicExplodedTransformTower as Tower

private
  variable
    ℓG ℓC ℓB ℓX ℓD : Level
    G : Set ℓG
    C : Set ℓC

cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
  (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

record AffineWarp (G : Set ℓG) : Set ℓG where
  field
    map : G → G
    inverse : G → G
    leftInverse : (g : G) → inverse (map g) ≡ g
    rightInverse : (g : G) → map (inverse g) ≡ g

open AffineWarp public

identityAffine : AffineWarp G
identityAffine = record
  { map = λ g → g
  ; inverse = λ g → g
  ; leftInverse = λ g → refl
  ; rightInverse = λ g → refl
  }

composeAffine : AffineWarp G → AffineWarp G → AffineWarp G
composeAffine outer inner = record
  { map = λ g → map outer (map inner g)
  ; inverse = λ g → inverse inner (inverse outer g)
  ; leftInverse = λ g →
      trans (cong (inverse inner) (leftInverse outer (map inner g)))
            (leftInverse inner g)
  ; rightInverse = λ g →
      trans (cong (map outer) (rightInverse inner (inverse outer g)))
            (rightInverse outer g)
  }

pullback-identity :
  (s : Tower.State G C) → (g : G) → (c : C) →
  Tower.pullback (map identityAffine) s g c ≡ s g c
pullback-identity s g c = refl

pullback-composition :
  (outer inner : AffineWarp G) → (s : Tower.State G C) →
  (g : G) → (c : C) →
  Tower.pullback (map (composeAffine outer inner)) s g c
  ≡ Tower.pullback (map inner) (Tower.pullback (map outer) s) g c
pullback-composition outer inner s g c = refl

pullback-inverse-left :
  (a : AffineWarp G) → (s : Tower.State G C) → (g : G) → (c : C) →
  Tower.pullback (inverse a) (Tower.pullback (map a) s) g c ≡ s g c
pullback-inverse-left a s g c = cong (λ x → s x c) (leftInverse a g)

pullback-inverse-right :
  (a : AffineWarp G) → (s : Tower.State G C) → (g : G) → (c : C) →
  Tower.pullback (map a) (Tower.pullback (inverse a) s) g c ≡ s g c
pullback-inverse-right a s g c = cong (λ x → s x c) (rightInverse a g)

record StronglyNoninterfering
  (a b : Tower.AtomicTransform G) : Set ℓG where
  field
    exclusive : (g : G) → Tower.support a g ≡ true →
      Tower.support b g ≡ true → ⊥
    aSourceOutsideB : (g : G) → Tower.support a g ≡ true →
      Tower.support b (Tower.localWarp a g) ≡ false
    bSourceOutsideA : (g : G) → Tower.support b g ≡ true →
      Tower.support a (Tower.localWarp b g) ≡ false

open StronglyNoninterfering public

atomic-commutes-under-noninterference :
  (a b : Tower.AtomicTransform G) → StronglyNoninterfering a b →
  (s : Tower.State G C) → (g : G) → (c : C) →
  Tower.applyAtomic a (Tower.applyAtomic b s) g c
  ≡ Tower.applyAtomic b (Tower.applyAtomic a s) g c
atomic-commutes-under-noninterference a b ni s g c
  with Tower.support a g | Tower.support b g
... | false | false = refl
... | true | false rewrite aSourceOutsideB ni g refl = refl
... | false | true rewrite bSourceOutsideA ni g refl = refl
... | true | true = ⊥-elim (exclusive ni g refl refl)

data CodecPartitionDigit : Set where
  branch3 branch6 branch9 : CodecPartitionDigit

CodecPartitionAddress : Nat → Set
CodecPartitionAddress d = Vec CodecPartitionDigit d

toSSPDigit : CodecPartitionDigit → U369.Digit369
toSSPDigit branch3 = U369.digit3
toSSPDigit branch6 = U369.digit6
toSSPDigit branch9 = U369.digit9

fromSSPDigit : U369.Digit369 → CodecPartitionDigit
fromSSPDigit U369.digit3 = branch3
fromSSPDigit U369.digit6 = branch6
fromSSPDigit U369.digit9 = branch9

toSSPDigit-fromSSPDigit : ∀ d → toSSPDigit (fromSSPDigit d) ≡ d
toSSPDigit-fromSSPDigit U369.digit3 = refl
toSSPDigit-fromSSPDigit U369.digit6 = refl
toSSPDigit-fromSSPDigit U369.digit9 = refl

fromSSPDigit-toSSPDigit : ∀ d → fromSSPDigit (toSSPDigit d) ≡ d
fromSSPDigit-toSSPDigit branch3 = refl
fromSSPDigit-toSSPDigit branch6 = refl
fromSSPDigit-toSSPDigit branch9 = refl

toSSPAddress : ∀ {d} → CodecPartitionAddress d → U369.Address d
toSSPAddress [] = []
toSSPAddress (x ∷ xs) = toSSPDigit x ∷ toSSPAddress xs

fromSSPAddress : ∀ {d} → U369.Address d → CodecPartitionAddress d
fromSSPAddress [] = []
fromSSPAddress (x ∷ xs) = fromSSPDigit x ∷ fromSSPAddress xs

toSSP-fromSSP-address : ∀ {d} (a : U369.Address d) →
  toSSPAddress (fromSSPAddress a) ≡ a
toSSP-fromSSP-address [] = refl
toSSP-fromSSP-address (x ∷ xs) rewrite toSSPDigit-fromSSPDigit x =
  cong (λ tail → x ∷ tail) (toSSP-fromSSP-address xs)

fromSSP-toSSP-address : ∀ {d} (a : CodecPartitionAddress d) →
  fromSSPAddress (toSSPAddress a) ≡ a
fromSSP-toSSP-address [] = refl
fromSSP-toSSP-address (x ∷ xs) rewrite fromSSPDigit-toSSPDigit x =
  cong (λ tail → x ∷ tail) (fromSSP-toSSP-address xs)

codecDistance : ∀ {d} → CodecPartitionAddress d → CodecPartitionAddress d → Nat
codecDistance x y = U369.distance (toSSPAddress x) (toSSPAddress y)

addressBridge-preserves-distance : ∀ {d} (x y : CodecPartitionAddress d) →
  U369.distance (toSSPAddress x) (toSSPAddress y) ≡ codecDistance x y
addressBridge-preserves-distance x y = refl

addressBridge-reflects-equality : ∀ {d} {x y : CodecPartitionAddress d} →
  toSSPAddress x ≡ toSSPAddress y → x ≡ y
addressBridge-reflects-equality {x = x} {y = y} eq =
  trans (sym (fromSSP-toSSP-address x))
        (trans (cong fromSSPAddress eq) (fromSSP-toSSP-address y))

record ChartCost : Set where
  constructor chartCost
  field sideBits residualBits : Nat

open ChartCost public

chartDescriptionLength : ChartCost → Nat
chartDescriptionLength c = sideBits c + residualBits c

record ChartRefinementBound (before after : ChartCost) : Set where
  field
    sideNonincrease : sideBits after ≤ sideBits before
    residualNonincrease : residualBits after ≤ residualBits before

open ChartRefinementBound public

chart-refinement-implies-mdl-nonincreasing : ∀ {before after} →
  ChartRefinementBound before after →
  chartDescriptionLength after ≤ chartDescriptionLength before
chart-refinement-implies-mdl-nonincreasing bound =
  NatP.+-mono-≤ (sideNonincrease bound) (residualNonincrease bound)

record StrictChartMDLDescent (before after : ChartCost) : Set where
  field
    nonincrease : chartDescriptionLength after ≤ chartDescriptionLength before
    strictWitness : chartDescriptionLength after ≡ chartDescriptionLength before → ⊥

record MetricQualifiedApproximation
  (X : Set ℓX) (Block : Set ℓB) (D : Set ℓD) :
  Set (lsuc (ℓX ⊔ ℓB ⊔ ℓD)) where
  field
    leafOf : X → Block
    target : X → X
    localAffine : Block → X → X
    distance : X → X → D
    tolerance : D
    Within : D → D → Set ℓD
    localApproximation : (x : X) →
      Within (distance (localAffine (leafOf x) x) (target x)) tolerance

open MetricQualifiedApproximation public

piecewiseAffine : ∀ {X : Set ℓX} {Block : Set ℓB} {D : Set ℓD} →
  MetricQualifiedApproximation X Block D → X → X
piecewiseAffine problem x = localAffine problem (leafOf problem x) x

piecewise-affine-inherits-local-bound :
  ∀ {X : Set ℓX} {Block : Set ℓB} {D : Set ℓD} →
  (problem : MetricQualifiedApproximation X Block D) → (x : X) →
  Within problem
    (distance problem (piecewiseAffine problem x) (target problem x))
    (tolerance problem)
piecewise-affine-inherits-local-bound problem x = localApproximation problem x
