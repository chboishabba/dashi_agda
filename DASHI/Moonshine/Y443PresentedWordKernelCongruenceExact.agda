module DASHI.Moonshine.Y443PresentedWordKernelCongruenceExact where

------------------------------------------------------------------------
-- Y443 V2: the literal selected-group interpretation kernel on
-- ORIGINAL signed Coxeter node expressions.
--
-- This is an actual equivalence and two-sided multiplication congruence,
-- not an abstract quotient isomorphism interface. It identifies the
-- precise missing V2 fact: equality in the UNIVERSAL 80-relator
-- presentation must be equivalent to equality in the selected group.
--
-- A homomorphism induced by relator satisfaction may have a larger
-- kernel; signed-word surjectivity alone does not imply faithfulness.
--
-- Sources: Ivanov (1999), Bray's Y443/Monster presentation;
-- JMD / meta-introspector for independent two-generator recovery.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443PresentedGroupNodeGenerationExact as Presented

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

cong : ∀ {A B : Set} (f : A → B) {x y : A} →
  x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C)
  {x y : A} {z w : B} → x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

module Kernel {G : Set}
    (gi : TM.GroupWithInverse G)
    (nodes : Y.Node → G) where

  Expr : Set
  Expr = Presented.SignedNodeExpression

  eval : Expr → G
  eval = Presented.interpret gi nodes

  infix 4 _≈_
  _≈_ : Expr → Expr → Set
  x ≈ y = eval x ≡ eval y

  reflexive : (x : Expr) → x ≈ x
  reflexive x = refl

  symmetric : ∀ {x y : Expr} → x ≈ y → y ≈ x
  symmetric = sym

  transitive : ∀ {x y z : Expr} → x ≈ y → y ≈ z → x ≈ z
  transitive = trans

  multiplyCongruence :
    ∀ {a b c d : Expr} → a ≈ b → c ≈ d →
    Presented.multiply a c ≈ Presented.multiply b d
  multiplyCongruence = cong₂ (Pair.multiply gi)

  inverseCongruence :
    ∀ {a b : Expr} → a ≈ b →
    Presented.inverse a ≈ Presented.inverse b
  inverseCongruence = cong (Pair.inverse gi)

  generatorReflexive : (n : Y.Node) →
    Presented.generator n ≈ Presented.generator n
  generatorReflexive n = refl

  -- Every selected group element has a representative if and only if
  -- an ORIGINAL signed-node surjectivity witness is supplied.
  -- This is not a universal-presentation injectivity assertion.
  selectedRepresentative :
    Presented.PresentedByY443Nodes gi nodes →
    (g : G) → Presented.SyntaxWitness gi nodes g
  selectedRepresentative source = Presented.allElementsHaveSourceWords source

  -- The missing V2 theorem is the reverse comparison to equality in
  -- the true presented word quotient. Neither this kernel congruence
  -- nor original relator satisfaction can manufacture that comparison.
