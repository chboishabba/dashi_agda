module DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact where

------------------------------------------------------------------------
-- Complete the ALGEBRAIC half of JMD's w^5/w^6 lemma.
-- No postulate: generic GroupWithInverse, associative multiplication,
-- explicit inverse, and the three genuine Coxeter-path source premises:
--   x4^2 = 1, beta^5 = 1, x4*beta = beta*x4.
--
-- This proves (x4*beta)^5=x4 and (x4*beta)^6=beta,
-- and discharges the 2 power fields of JMDConcretePowers.
-- The original Y443 group must still provide those three premises via
-- the selected Coxeter-path relation proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDTracePowerExact as Power
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMD
import DASHI.Moonshine.Y443JMDConcretePairPowerCompilerExact as Compiler
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C)
  {x y : A} {z w : B} →
  x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

module PowerAlgebra {G : Set} (gi : TM.GroupWithInverse G) where
  g : GR.Group G
  g = TM.GroupWithInverse.group gi

  e : G
  e = GR.Group.identity g

  mul : G → G → G
  mul = GR.Group._∙_ g

  inv : G → G
  inv = TM.GroupWithInverse.inverse gi

  pow : G → Nat → G
  pow = Power.groupPower gi

  assoc : (a b c : G) → mul (mul a b) c ≡ mul a (mul b c)
  assoc = GR.Group.associativity g

  leftId : (x : G) → mul e x ≡ x
  leftId = GR.Group.leftIdentity g

  rightId : (x : G) → mul x e ≡ x
  rightId x =
    trans
      (cong (mul x) (sym (TM.GroupWithInverse.leftInverse gi x)))
      (trans
        (sym (assoc x (inv x) x))
        (trans
          (cong (λ y → mul y x)
            (TM.GroupWithInverse.rightInverse gi x))
          (leftId x)))

  powOne : (x : G) → pow x 1 ≡ x
  powOne = rightId

  powTwoStep : (x : G) →
    mul x x ≡ e →
    (n : Nat) → pow x (suc (suc n)) ≡ pow x n
  powTwoStep x hx n =
    trans
      (sym (assoc x x (pow x n)))
      (trans
        (cong (λ y → mul y (pow x n)) hx)
        (leftId (pow x n)))

  powFiveOfInvolution : (x : G) → mul x x ≡ e → pow x 5 ≡ x
  powFiveOfInvolution x hx =
    trans
      (powTwoStep x hx 3)
      (trans (powTwoStep x hx 1) (powOne x))

  powSixOfInvolution : (x : G) → mul x x ≡ e → pow x 6 ≡ e
  powSixOfInvolution x hx =
    trans (powTwoStep x hx 4)
      (trans (powTwoStep x hx 2)
        (powTwoStep x hx 0))

  powSixOfOrderFive :
    (x : G) → pow x 5 ≡ e → pow x 6 ≡ x
  powSixOfOrderFive x hx =
    trans
      (cong (mul x) hx)
      (rightId x)

  commutesWithPowers :
    (x b : G) → mul x b ≡ mul b x →
    (n : Nat) → mul b (pow x n) ≡ mul (pow x n) b
  commutesWithPowers x b comm zero =
    trans (rightId b) (sym (leftId b))
  commutesWithPowers x b comm (suc n) =
    trans
      (sym (assoc b x (pow x n)))
      (trans
        (cong (λ y → mul y (pow x n)) (sym comm))
        (trans
          (assoc x b (pow x n))
          (trans
            (cong (mul x) (commutesWithPowers x b comm n))
            (sym (assoc x (pow x n) b)))))

  powCommutingProduct :
    (x b : G) → mul x b ≡ mul b x →
    (n : Nat) →
    pow (mul x b) n ≡ mul (pow x n) (pow b n)
  powCommutingProduct x b comm zero =
    sym (leftId e)
  powCommutingProduct x b comm (suc n) =
    trans
      (cong (mul (mul x b)) (powCommutingProduct x b comm n))
      (trans
        (assoc x b (mul (pow x n) (pow b n)))
        (trans
          (cong (mul x) (sym (assoc b (pow x n) (pow b n))))
          (trans
            (cong (λ z → mul x (mul z (pow b n)))
              (commutesWithPowers x b comm n))
            (trans
              (cong (mul x) (assoc (pow x n) b (pow b n)))
              (sym (assoc x (pow x n) (mul b (pow b n))))))))

  fifthProductIsFirst :
    (x b : G) →
    mul x x ≡ e →
    pow b 5 ≡ e →
    mul x b ≡ mul b x →
    pow (mul x b) 5 ≡ x
  fifthProductIsFirst x b x2 b5 comm =
    trans
      (powCommutingProduct x b comm 5)
      (trans
        (cong₂ mul (powFiveOfInvolution x x2) b5)
        (rightId x))

  sixthProductIsSecond :
    (x b : G) →
    mul x x ≡ e →
    pow b 5 ≡ e →
    mul x b ≡ mul b x →
    pow (mul x b) 6 ≡ b
  sixthProductIsSecond x b x2 b5 comm =
    trans
      (powCommutingProduct x b comm 6)
      (trans
        (cong₂ mul
          (powSixOfInvolution x x2)
          (powSixOfOrderFive b b5))
        (leftId b))

------------------------------------------------------------------------
-- Source-exact selected Y443 JMD instance, no external power fields.
------------------------------------------------------------------------

record JMDSourcePathPremises
  {G : Set} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) : Set where
  field
    x4Square :
      Pair.multiply gi (nodes JMD.x4) (nodes JMD.x4) ≡ Pair.identity gi
    betaOrderFive :
      Power.groupPower gi (JMD.betaElement gi nodes) 5 ≡ Pair.identity gi
    x4CommutesBeta :
      Pair.multiply gi (nodes JMD.x4) (JMD.betaElement gi nodes) ≡
      Pair.multiply gi (JMD.betaElement gi nodes) (nodes JMD.x4)

open JMDSourcePathPremises public

deriveConcretePowers :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  JMDSourcePathPremises gi nodes →
  Compiler.JMDConcretePowers gi nodes
deriveConcretePowers gi nodes prem =
  let
    module P = PowerAlgebra gi
    x = nodes JMD.x4
    b = JMD.betaElement gi nodes
    hw = JMD.wIsX4Beta gi nodes
    x5 = P.fifthProductIsFirst x b
      (x4Square prem) (betaOrderFive prem) (x4CommutesBeta prem)
    b6 = P.sixthProductIsSecond x b
      (x4Square prem) (betaOrderFive prem) (x4CommutesBeta prem)
  in record
    { Compiler.sourceX4Fifth =
      sym (trans (cong (λ y → P.pow y 5) hw) x5)
    ; Compiler.sourceBetaSixth =
      sym (trans (cong (λ y → P.pow y 6) hw) b6)
    }
