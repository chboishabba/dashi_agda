module DASHI.Physics.YangMills.BalabanSU2AveragingSection where

------------------------------------------------------------------------
-- Constructive sections for the linearized averaging operator.
--
-- This file proves the algebraic part of the small-background argument rather
-- than storing surjectivity as a field.  A literal zero-background section S0
-- and a two-sided inverse for I + E S0 produce the corrected section
--
--   SB = S0 (I + E S0)^-1,
--
-- and Q(B) SB = I follows by equality reasoning.  Analytic work is isolated to
-- constructing the inverse and its norm bound; the right-inverse theorem itself
-- is exact and assumption-minimal.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

infixr 9 _∘_

_∘_ :
  ∀ {a b c}
  {A : Set a} {B : Set b} {C : Set c} →
  (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

RightInverse :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c} →
  (Fine → Coarse) → (Coarse → Fine) → Set (f ⊔ c)
RightInverse Q S = ∀ coarse → Q (S coarse) ≡ coarse

Surjective :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c} →
  (Fine → Coarse) → Set (f ⊔ c)
Surjective Q = ∀ coarse → Σ _ (λ fine → Q fine ≡ coarse)

Injective :
  ∀ {a b}
  {A : Set a} {B : Set b} →
  (A → B) → Set (a ⊔ b)
Injective f = ∀ {left right} → f left ≡ f right → left ≡ right

record AveragingSection
  {f c : Level}
  (Fine : Set f)
  (Coarse : Set c)
  (Q : Fine → Coarse) : Set (f ⊔ c) where
  constructor averagingSection
  field
    section : Coarse → Fine
    sectionRightInverse : RightInverse Q section

open AveragingSection public

sectionSurjective :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c}
  {Q : Fine → Coarse} →
  AveragingSection Fine Coarse Q →
  Surjective Q
sectionSurjective bundle coarse =
  section bundle coarse , sectionRightInverse bundle coarse

averagingConstraintsIndependent :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c}
  {Q : Fine → Coarse} →
  AveragingSection Fine Coarse Q →
  Surjective Q
averagingConstraintsIndependent = sectionSurjective

------------------------------------------------------------------------
-- Literal zero-background section.
------------------------------------------------------------------------

averagingSectionAtZero :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c}
  (Q0 : Fine → Coarse)
  (S0 : Coarse → Fine) →
  RightInverse Q0 S0 →
  AveragingSection Fine Coarse Q0
averagingSectionAtZero Q0 S0 Q0S0 =
  averagingSection S0 Q0S0

------------------------------------------------------------------------
-- Small-background correction.
--
-- M is the coarse operator I + E S0.  `middleDefinition` fixes that
-- interpretation exactly.  The theorem does not assume an opaque section for Q;
-- it constructs one and proves the right-inverse equation.
------------------------------------------------------------------------

smallBackgroundSectionMap :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c} →
  (S0 : Coarse → Fine) →
  (middleInverse : Coarse → Coarse) →
  Coarse → Fine
smallBackgroundSectionMap S0 middleInverse = S0 ∘ middleInverse

smallBackgroundSectionRightInverse :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c}
  (Q Q0 E : Fine → Coarse)
  (S0 : Coarse → Fine)
  (coarseAdd : Coarse → Coarse → Coarse)
  (middle middleInverse : Coarse → Coarse) →
  (qSplit : ∀ fine → Q fine ≡ coarseAdd (Q0 fine) (E fine)) →
  (Q0S0 : RightInverse Q0 S0) →
  (middleDefinition : ∀ coarse →
    middle coarse ≡ coarseAdd coarse (E (S0 coarse))) →
  (middleInverseRight : RightInverse middle middleInverse) →
  RightInverse Q (smallBackgroundSectionMap S0 middleInverse)
smallBackgroundSectionRightInverse
  Q Q0 E S0 coarseAdd middle middleInverse
  qSplit Q0S0 middleDefinition middleInverseRight coarse =
  trans
    (qSplit (S0 (middleInverse coarse)))
    (trans
      (cong
        (λ averaged → coarseAdd averaged (E (S0 (middleInverse coarse))))
        (Q0S0 (middleInverse coarse)))
      (trans
        (sym (middleDefinition (middleInverse coarse)))
        (middleInverseRight coarse)))

smallBackgroundSection :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c}
  (Q Q0 E : Fine → Coarse)
  (S0 : Coarse → Fine)
  (coarseAdd : Coarse → Coarse → Coarse)
  (middle middleInverse : Coarse → Coarse) →
  (qSplit : ∀ fine → Q fine ≡ coarseAdd (Q0 fine) (E fine)) →
  (Q0S0 : RightInverse Q0 S0) →
  (middleDefinition : ∀ coarse →
    middle coarse ≡ coarseAdd coarse (E (S0 coarse))) →
  (middleInverseRight : RightInverse middle middleInverse) →
  AveragingSection Fine Coarse Q
smallBackgroundSection
  Q Q0 E S0 coarseAdd middle middleInverse
  qSplit Q0S0 middleDefinition middleInverseRight =
  averagingSection
    (smallBackgroundSectionMap S0 middleInverse)
    (smallBackgroundSectionRightInverse
      Q Q0 E S0 coarseAdd middle middleInverse
      qSplit Q0S0 middleDefinition middleInverseRight)

backgroundAverageSurjective :
  ∀ {f c}
  {Fine : Set f} {Coarse : Set c}
  (Q Q0 E : Fine → Coarse)
  (S0 : Coarse → Fine)
  (coarseAdd : Coarse → Coarse → Coarse)
  (middle middleInverse : Coarse → Coarse) →
  (qSplit : ∀ fine → Q fine ≡ coarseAdd (Q0 fine) (E fine)) →
  (Q0S0 : RightInverse Q0 S0) →
  (middleDefinition : ∀ coarse →
    middle coarse ≡ coarseAdd coarse (E (S0 coarse))) →
  (middleInverseRight : RightInverse middle middleInverse) →
  Surjective Q
backgroundAverageSurjective
  Q Q0 E S0 coarseAdd middle middleInverse
  qSplit Q0S0 middleDefinition middleInverseRight =
  sectionSurjective
    (smallBackgroundSection
      Q Q0 E S0 coarseAdd middle middleInverse
      qSplit Q0S0 middleDefinition middleInverseRight)

------------------------------------------------------------------------
-- Any explicit left inverse proves injectivity.  In the Hilbert-space
-- instantiation the left inverse is S* and the map is Q*, so a constructed
-- averaging section proves that the adjoint constraints are independent too.
------------------------------------------------------------------------

leftInverseForcesInjective :
  ∀ {a b}
  {A : Set a} {B : Set b}
  (forward : A → B)
  (back : B → A) →
  (∀ x → back (forward x) ≡ x) →
  Injective forward
leftInverseForcesInjective forward back leftInverse {left} {right} equality =
  trans
    (sym (leftInverse left))
    (trans (cong back equality) (leftInverse right))

sectionForcesAdjointInjective :
  ∀ {c f}
  {Coarse : Set c} {Fine : Set f}
  (averageStar : Coarse → Fine)
  (sectionStar : Fine → Coarse) →
  (∀ coarse → sectionStar (averageStar coarse) ≡ coarse) →
  Injective averageStar
sectionForcesAdjointInjective = leftInverseForcesInjective
