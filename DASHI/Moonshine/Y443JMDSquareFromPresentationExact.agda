module DASHI.Moonshine.Y443JMDSquareFromPresentationExact where

------------------------------------------------------------------------
-- The x4 involution is one of the 12 ACTUAL source relators:
-- x4=e1 is the 5th node in the Y443 source alphabet.
-- Extract its evaluated square directly from RelatorsSatisfied,
-- and then eliminate the trailing identity by the derived GROUP law.
--
-- This eliminates x4Square as an independent source assumption.
-- No parameterized "assume involution" substitution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
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

-- Y.monsterRelators begins with map square Y.nodes; its fifth entry
-- is the exact x4=e1 square, not an arbitrary word.
fifthNodeSquareRelator :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  Pair.RelatorsSatisfied gi nodes Y.monsterRelators →
  Pair.evaluateCoxeterWord gi nodes (Y.square JMD.x4) ≡
  Pair.identity gi
fifthNodeSquareRelator gi nodes all =
  Pair._∧_.left
    (Pair._∧_.right
      (Pair._∧_.right
        (Pair._∧_.right
          (Pair._∧_.right all))))

squareFromActualPresentation :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  Pair.RelatorsSatisfied gi nodes Y.monsterRelators →
  Pair.multiply gi (nodes JMD.x4) (nodes JMD.x4) ≡ Pair.identity gi
squareFromActualPresentation gi nodes all =
  let
    module P = Power.PowerAlgebra gi
    x = nodes JMD.x4
    raw = fifthNodeSquareRelator gi nodes all
  in trans
    (sym (cong (P.mul x) (P.rightId x)))
    raw
