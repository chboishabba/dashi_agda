module DASHI.Moonshine.Y443CoxeterRelatorSemanticLawsExact where

------------------------------------------------------------------------
-- Generic source soundness of the Y443 m=2 / m=3 Coxeter words.
--
-- This module goes BEYOND Boolean adjacency: the selected group
-- literally satisfies the original 80 Y443 word relators. From the
-- word evaluation, derive:
-- * x^2=1 for each selected node;
-- * (xy)^2=1 for nonadjacent nodes -> commute (existing owner);
-- * (xy)^3=1 for adjacent nodes -> xyx=yxy.
--
-- All group results reuse the original inverse/associativity owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact as Power
import DASHI.Moonshine.Y443JMDNonadjacentRelatorConsequencesExact as Relations
import DASHI.Moonshine.TwistedModuleModularity as TM

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {x y : A} {z w : B} →
  x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

module Laws {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G)
  (all : Pair.RelatorsSatisfied gi nodes Y.monsterRelators) where

  module P = Power.PowerAlgebra gi
  module R = Relations.SourceConsequences gi nodes all
  open P using (e; mul; inv; pow; assoc; leftId; rightId)

  evalConcat :
    (u v : Y.Word) →
    Pair.evaluateCoxeterWord gi nodes (Y._++_ u v)
    ≡ mul (Pair.evaluateCoxeterWord gi nodes u)
          (Pair.evaluateCoxeterWord gi nodes v)
  evalConcat [] v = sym (leftId (Pair.evaluateCoxeterWord gi nodes v))
  evalConcat (x ∷ xs) v =
    trans
      (cong (mul (nodes x)) (evalConcat xs v))
      (sym (assoc (nodes x)
        (Pair.evaluateCoxeterWord gi nodes xs)
        (Pair.evaluateCoxeterWord gi nodes v)))

  evalPower :
    (u : Y.Word) (n : Nat) →
    Pair.evaluateCoxeterWord gi nodes (Y.powerWord u n)
    ≡ pow (Pair.evaluateCoxeterWord gi nodes u) n
  evalPower u zero = refl
  evalPower u (suc n) =
    trans
      (evalConcat u (Y.powerWord u n))
      (cong (mul (Pair.evaluateCoxeterWord gi nodes u))
        (evalPower u n))

  pairWordAsProduct :
    (x y : Y.Node) →
    Pair.evaluateCoxeterWord gi nodes (x ∷ y ∷ []) ≡
    mul (nodes x) (nodes y)
  pairWordAsProduct x y =
    cong (mul (nodes x)) (rightId (nodes y))

  edgeProductCube :
    (x y : Y.Node) →
    (member :
      Relations._∈_ (Y.pairRelator (Y.pair x y)) Y.monsterRelators) →
    Y.adjacent x y ≡ true →
    pow (mul (nodes x) (nodes y)) 3 ≡ e
  edgeProductCube x y member isAdjacent rewrite isAdjacent =
    trans
      (sym (cong (λ z → pow z 3) (pairWordAsProduct x y)))
      (trans
        (sym (evalPower (x ∷ y ∷ []) 3))
        (Relations.relatorMembershipElim gi nodes
          (Y.pairRelator (Y.pair x y)) member all))

  powThreeAsLeftInverse :
    (z : G) →
    pow z 3 ≡ e →
    mul (mul z z) z ≡ e
  powThreeAsLeftInverse z power3 =
    trans
      (assoc z z z)
      (trans
        (cong (λ q → mul z (mul z q)) (sym (rightId z)))
        power3)

  braidFromCoxeter :
    (x y : G) →
    mul x x ≡ e →
    mul y y ≡ e →
    pow (mul x y) 3 ≡ e →
    mul x (mul y x) ≡ mul y (mul x y)
  braidFromCoxeter x y xx yy cube =
    let
      t = mul x y
      ttt = powThreeAsLeftInverse t cube
      squaredIsInverse = R.leftInverseUnique (mul t t) t ttt
      inverseIsYX =
        trans
          squaredIsInverse
          (trans
            (sym (R.inverseProduct x y))
            (cong₂ mul
              (sym (R.leftInverseUnique y y yy))
              (sym (R.leftInverseUnique x x xx))))
      leftProduct :
        mul (mul t t) y ≡ mul x (mul y x)
      leftProduct =
        trans
          (assoc t t y)
          (trans
            (cong (mul t)
              (trans
                (assoc x y y)
                (trans (cong (mul x) yy) (rightId x))))
            (assoc x y x))
    in
    trans (sym leftProduct)
      (trans
        (cong (λ q → mul q y) inverseIsYX)
        (assoc y x y))

  edgeBraid :
    (x y : Y.Node) →
    Y.pairRelator (Y.pair x y) Relations.∈ Y.monsterRelators →
    Relations._∈_ (Y.square x) Y.monsterRelators →
    Relations._∈_ (Y.square y) Y.monsterRelators →
    Y.adjacent x y ≡ true →
    mul (nodes x) (mul (nodes y) (nodes x)) ≡
    mul (nodes y) (mul (nodes x) (nodes y))
  edgeBraid x y edgeMember xMember yMember isAdjacent =
    braidFromCoxeter (nodes x) (nodes y)
      (R.squareFrom x xMember)
      (R.squareFrom y yMember)
      (edgeProductCube x y edgeMember isAdjacent)
