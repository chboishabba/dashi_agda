module DASHI.Moonshine.Y443JMDNonadjacentRelatorConsequencesExact where

------------------------------------------------------------------------
-- Exact four Y443 x4-beta NONADJACENT COMMUTATIONS.
-- All five involution squares + four nonedge pair relators are EXTRACTED
-- from actual original 80 relation words using proof-relevant membership.
-- Classical inverse uniqueness then derives xy=yx, not merely Bool tags.
--
-- The original selected presentation group is still an INPUT:
-- its RelatorsSatisfied witness must refer to the SAME node interpretation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMD
import DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact as Power
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

infix 4 _∈_
data _∈_ (w : Y.Word) : List Y.Word → Set where
  here : ∀ {ws} → w ∈ (w ∷ ws)
  there : ∀ {v ws} → w ∈ ws → w ∈ (v ∷ ws)

relatorMembershipElim :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  (w : Y.Word) {words : List Y.Word} →
  w ∈ words →
  Pair.RelatorsSatisfied gi nodes words →
  Pair.evaluateCoxeterWord gi nodes w ≡ Pair.identity gi
relatorMembershipElim gi nodes w here holds = Pair._∧_.left holds
relatorMembershipElim gi nodes w (there member) holds =
  relatorMembershipElim gi nodes w member (Pair._∧_.right holds)

------------------------------------------------------------------------
-- Exact witnesses: 5th-9th square and 51st-54th relation indices
-- (0-based 4..8 and 50..53). These are not invented group axioms.
------------------------------------------------------------------------

memberSquaree1 : Y.square Y.e1 ∈ Y.monsterRelators
memberSquaree1 = there (there (there (there (here))))

memberSquareb2 : Y.square Y.b2 ∈ Y.monsterRelators
memberSquareb2 = there (there (there (there (there (here)))))

memberSquarec2 : Y.square Y.c2 ∈ Y.monsterRelators
memberSquarec2 = there (there (there (there (there (there (here))))))

memberSquared2 : Y.square Y.d2 ∈ Y.monsterRelators
memberSquared2 = there (there (there (there (there (there (there (here)))))))

memberSquaree2 : Y.square Y.e2 ∈ Y.monsterRelators
memberSquaree2 = there (there (there (there (there (there (there (there (here))))))))

memberPairE1b2 : Y.pairRelator (Y.pair Y.e1 Y.b2) ∈ Y.monsterRelators
memberPairE1b2 = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))))))))))))))))))))))))))))))))))))))

memberPairE1c2 : Y.pairRelator (Y.pair Y.e1 Y.c2) ∈ Y.monsterRelators
memberPairE1c2 = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))))))))))))))))))))))))))))))))))))))

memberPairE1d2 : Y.pairRelator (Y.pair Y.e1 Y.d2) ∈ Y.monsterRelators
memberPairE1d2 = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))))))))))))))))))))))))))))))))))))))))

memberPairE1e2 : Y.pairRelator (Y.pair Y.e1 Y.e2) ∈ Y.monsterRelators
memberPairE1e2 = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))))))))))))))))))))))))))))))))))))))))


------------------------------------------------------------------------
-- Translate actual source word evaluations to x*x=e, (x*y)^2=e.
------------------------------------------------------------------------

module SourceConsequences {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G)
  (all : Pair.RelatorsSatisfied gi nodes Y.monsterRelators) where

  module P = Power.PowerAlgebra gi
  open P using (e; mul; inv; assoc; leftId; rightId)

  squareFrom : (n : Y.Node) →
    Y.square n ∈ Y.monsterRelators →
    mul (nodes n) (nodes n) ≡ e
  squareFrom n member =
    trans
      (sym (cong (mul (nodes n)) (rightId (nodes n))))
      (relatorMembershipElim gi nodes (Y.square n) member all)

  nonedgeProductSquare :
    (x y : Y.Node) →
    Y.pairRelator (Y.pair x y) ∈ Y.monsterRelators →
    Y.adjacent x y ≡ Agda.Builtin.Bool.false →
    mul (mul (nodes x) (nodes y))
      (mul (nodes x) (nodes y)) ≡ e
  nonedgeProductSquare x y member notAdjacent =
    let
      a = nodes x
      b = nodes y
      raw = relatorMembershipElim gi nodes
        (Y.pairRelator (Y.pair x y)) member all
    in trans
      (assoc a b (mul a b))
      (trans
        (cong (λ z → mul a (mul b z))
          (cong (mul a) (sym (rightId b))))
        raw)

  leftInverseUnique :
    (a z : G) → mul a z ≡ e → a ≡ inv z
  leftInverseUnique a z az =
    trans
      (sym (rightId a))
      (trans
        (cong (mul a) (sym (TM.GroupWithInverse.rightInverse gi z)))
        (trans
          (sym (assoc a z (inv z)))
          (trans
            (cong (λ q → mul q (inv z)) az)
            (leftId (inv z)))))

  inverseProduct : (x y : G) →
    mul (inv y) (inv x) ≡ inv (mul x y)
  inverseProduct x y =
    leftInverseUnique (mul (inv y) (inv x)) (mul x y)
      (trans
        (assoc (inv y) (inv x) (mul x y))
        (trans
          (cong (mul (inv y))
            (sym (assoc (inv x) x y)))
          (trans
            (cong (λ z → mul (inv y) (mul z y))
              (TM.GroupWithInverse.leftInverse gi x))
            (trans
              (cong (mul (inv y)) (leftId y))
              (TM.GroupWithInverse.leftInverse gi y)))))

  commuteFromThreeSquares :
    (x y : G) →
    mul x x ≡ e →
    mul y y ≡ e →
    mul (mul x y) (mul x y) ≡ e →
    mul x y ≡ mul y x
  commuteFromThreeSquares x y xx yy xyxy =
    trans
      (leftInverseUnique (mul x y) (mul x y) xyxy)
      (trans
        (sym (inverseProduct x y))
        (cong₂ mul
          (sym (leftInverseUnique y y yy))
          (sym (leftInverseUnique x x xx))))

  e1Squared : mul (nodes JMD.x4) (nodes JMD.x4) ≡ e
  e1Squared = squareFrom JMD.x4 memberSquaree1


  b2Squared : mul (nodes Y.b2) (nodes Y.b2) ≡ e
  b2Squared = squareFrom Y.b2 memberSquareb2

  e1Commutesb2 :
    mul (nodes JMD.x4) (nodes Y.b2)
    ≡ mul (nodes Y.b2) (nodes JMD.x4)
  e1Commutesb2 =
    commuteFromThreeSquares (nodes JMD.x4) (nodes Y.b2)
      e1Squared b2Squared
      (nonedgeProductSquare JMD.x4 Y.b2
        memberPairE1b2 refl)


  c2Squared : mul (nodes Y.c2) (nodes Y.c2) ≡ e
  c2Squared = squareFrom Y.c2 memberSquarec2

  e1Commutesc2 :
    mul (nodes JMD.x4) (nodes Y.c2)
    ≡ mul (nodes Y.c2) (nodes JMD.x4)
  e1Commutesc2 =
    commuteFromThreeSquares (nodes JMD.x4) (nodes Y.c2)
      e1Squared c2Squared
      (nonedgeProductSquare JMD.x4 Y.c2
        memberPairE1c2 refl)


  d2Squared : mul (nodes Y.d2) (nodes Y.d2) ≡ e
  d2Squared = squareFrom Y.d2 memberSquared2

  e1Commutesd2 :
    mul (nodes JMD.x4) (nodes Y.d2)
    ≡ mul (nodes Y.d2) (nodes JMD.x4)
  e1Commutesd2 =
    commuteFromThreeSquares (nodes JMD.x4) (nodes Y.d2)
      e1Squared d2Squared
      (nonedgeProductSquare JMD.x4 Y.d2
        memberPairE1d2 refl)


  e2Squared : mul (nodes Y.e2) (nodes Y.e2) ≡ e
  e2Squared = squareFrom Y.e2 memberSquaree2

  e1Commutese2 :
    mul (nodes JMD.x4) (nodes Y.e2)
    ≡ mul (nodes Y.e2) (nodes JMD.x4)
  e1Commutese2 =
    commuteFromThreeSquares (nodes JMD.x4) (nodes Y.e2)
      e1Squared e2Squared
      (nonedgeProductSquare JMD.x4 Y.e2
        memberPairE1e2 refl)


  e1CommutesBeta :
    mul (nodes JMD.x4) (JMD.betaElement gi nodes)
    ≡ mul (JMD.betaElement gi nodes) (nodes JMD.x4)
  e1CommutesBeta =
    let
      x = nodes JMD.x4
      b = nodes Y.b2
      c = nodes Y.c2
      d = nodes Y.d2
      f = nodes Y.e2
      -- beta's last expression ends in a trailing identity because the
      -- source Word evaluator is a right fold.
      betaFold =
        cong (λ z → mul b (mul c (mul d z))) (rightId f)
    in
    trans
      (cong (mul x) betaFold)
      (trans
        (sym (assoc x b (mul c (mul d f))))
        (trans
          (cong (λ z → mul z (mul c (mul d f))) e1Commutesb2)
          (assoc b x (mul c (mul d f)))))
