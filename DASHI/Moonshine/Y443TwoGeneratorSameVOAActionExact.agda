module DASHI.Moonshine.Y443TwoGeneratorSameVOAActionExact where

------------------------------------------------------------------------
-- ORIGINAL JMD U/V GENERATION => SAME-GROUP ACTION AGREEMENT
--
-- If two genuine actions of the EXACT selected group G on the EXACT same
-- state set agree on JMD generators u and v, they agree for EVERY g in G.
-- No group isomorphism, dimension identification or character equality is
-- used. The all-element u/v word is the original existing Y443 cover.
--
-- Important: VertexOperatorAlgebraCore.VOAGroupAction currently gives its
-- action-composition evidence only as an unrefined Set field. That field
-- cannot furnish the functional laws needed below. Therefore the exact
-- pointwise action laws are explicitly supplied rather than fabricated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.TwistedModuleModularity as TM

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C)
  {x y : A} {z w : B} → x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

record ActualGroupAction
  {G S : Set} (gi : TM.GroupWithInverse G) : Set where
  field
    act : G → S → S
    actsIdentity : (s : S) → act (Pair.identity gi) s ≡ s
    actsProduct : (g h : G) (s : S) →
      act (Pair.multiply gi g h) s ≡ act g (act h s)
    actsInverseLeft : (g : G) (s : S) →
      act (Pair.inverse gi g) (act g s) ≡ s
    actsInverseRight : (g : G) (s : S) →
      act g (act (Pair.inverse gi g) s) ≡ s
open ActualGroupAction public

actionsAgreeInverse :
  ∀ {G S : Set} (gi : TM.GroupWithInverse G) →
  (a b : ActualGroupAction {G} {S} gi) →
  (g : G) →
  ((s : S) → act a g s ≡ act b g s) →
  (s : S) →
  act a (Pair.inverse gi g) s
  ≡ act b (Pair.inverse gi g) s
actionsAgreeInverse gi a b g eq s =
  trans
    (sym (cong (act a (Pair.inverse gi g))
      (actsInverseRight b g s)))
    (trans
      (cong (act a (Pair.inverse gi g))
        (sym (eq (act b (Pair.inverse gi g) s))))
      (actsInverseLeft a g (act b (Pair.inverse gi g) s)))

actionsAgreeWord :
  ∀ {G S : Set} (gi : TM.GroupWithInverse G)
  (u v : G) (a b : ActualGroupAction {G} {S} gi) →
  ((s : S) → act a u s ≡ act b u s) →
  ((s : S) → act a v s ≡ act b v s) →
  (w : Pair.TwoWord) →
  (s : S) →
  act a (Pair.evaluate gi u v w) s
  ≡ act b (Pair.evaluate gi u v w) s
actionsAgreeWord gi u v a b eu ev Pair.emptyWord s =
  trans (actsIdentity a s) (sym (actsIdentity b s))
actionsAgreeWord gi u v a b eu ev Pair.leftGenerator s = eu s
actionsAgreeWord gi u v a b eu ev Pair.rightGenerator s = ev s
actionsAgreeWord gi u v a b eu ev (Pair.wordMultiply w z) s =
  trans
    (actsProduct a (Pair.evaluate gi u v w) (Pair.evaluate gi u v z) s)
    (trans
      (actionsAgreeWord gi u v a b eu ev w
        (act a (Pair.evaluate gi u v z) s))
      (trans
        (cong (act b (Pair.evaluate gi u v w))
          (actionsAgreeWord gi u v a b eu ev z s))
        (sym (actsProduct b
          (Pair.evaluate gi u v w) (Pair.evaluate gi u v z) s)))
actionsAgreeWord gi u v a b eu ev (Pair.wordInverse w) s =
  actionsAgreeInverse gi a b (Pair.evaluate gi u v w)
    (actionsAgreeWord gi u v a b eu ev w) s

actionsAgreeEntireY443 :
  ∀ {G S : Set} (weld : Pair.Y443VNaturalPairWeld G)
  (a b : ActualGroupAction {G} {S} (Pair.groupWithInverse weld)) →
  ((s : S) → act a (Pair.u weld) s ≡ act b (Pair.u weld) s) →
  ((s : S) → act a (Pair.v weld) s ≡ act b (Pair.v weld) s) →
  (g : G) → (s : S) →
  act a g s ≡ act b g s
actionsAgreeEntireY443 weld a b eu ev g s =
  trans
    (sym (cong (λ t → act a t s)
      (Pair.interpretation (Pair.cover weld g))))
    (trans
      (actionsAgreeWord (Pair.groupWithInverse weld)
        (Pair.u weld) (Pair.v weld)
        a b eu ev (Pair.word (Pair.cover weld g)) s)
      (cong (λ t → act b t s)
        (Pair.interpretation (Pair.cover weld g))))
