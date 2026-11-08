module DASHI.Moonshine.Y443FLMConcreteVOAGroupTransportExact where

------------------------------------------------------------------------
-- ACTUAL FLM -> SELECTED DASHI VOA / MONSTER ACTION TRANSPORT
--
-- This is a *concrete* preservation interface, NOT a dimension-label map:
-- vacuum, conformal element, all modes, translation, addition, scalar
-- action and EVERY homogeneous grade travel through two inverse state maps.
-- A same-scalar carrier is required: no unproved C -> F2 base change.
--
-- The group side is a genuine two-sided group equivalence between the
-- original Y443 selected group and the Monster carrier of the *published*
-- VOA action. Conjugation of its action along the exact state equivalence
-- gives a genuine Y443 action on the PREEXISTING selected VOA carrier.
--
-- Full faithfulness/every-automorphism classification is handled by the
-- existing Y443FLMGriessFullAutSelectedVOAExact; this file pays the
-- crucial group-action transport and only-U/V comparison interface.
-- No FLM model or isomorphism is fabricated by this record.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (ℤ)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443TwoGeneratorSameVOAActionExact as Action

sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

module Transport (selected published : VOA.VertexOperatorAlgebra) where

  module S where
    M = VOA.gradedModule selected
    Y = VOA.vertexData selected
    State = VOA.GradedModule.Carrier M
    Scalar = VOA.GradedModule.Scalar M
    Grade = VOA.GradedModule.gradePiece M
    include = VOA.GradedModule.includeGrade M

  module P where
    M = VOA.gradedModule published
    Y = VOA.vertexData published
    State = VOA.GradedModule.Carrier M
    Scalar = VOA.GradedModule.Scalar M
    Grade = VOA.GradedModule.gradePiece M
    include = VOA.GradedModule.includeGrade M

  record ExactFLMVOAIsomorphism : Setω where
    field
      toState : S.State → P.State
      fromState : P.State → S.State
      fromAfterTo : (x : S.State) → fromState (toState x) ≡ x
      toAfterFrom : (y : P.State) → toState (fromState y) ≡ y

      toScalar : S.Scalar → P.Scalar
      fromScalar : P.Scalar → S.Scalar
      scalarFromTo : (k : S.Scalar) → fromScalar (toScalar k) ≡ k
      scalarToFrom : (k : P.Scalar) → toScalar (fromScalar k) ≡ k

      toGrade : (n : Nat) → S.Grade n → P.Grade n
      fromGrade : (n : Nat) → P.Grade n → S.Grade n
      gradeFromTo : (n : Nat) (x : S.Grade n) →
        fromGrade n (toGrade n x) ≡ x
      gradeToFrom : (n : Nat) (x : P.Grade n) →
        toGrade n (fromGrade n x) ≡ x

      toIncludes : (n : Nat) (x : S.Grade n) →
        toState (S.include n x) ≡ P.include n (toGrade n x)
      fromIncludes : (n : Nat) (x : P.Grade n) →
        fromState (P.include n x) ≡ S.include n (fromGrade n x)

      toVacuum :
        toState (VOA.vacuum S.Y) ≡ VOA.vacuum P.Y
      toConformal :
        toState (VOA.conformalVector S.Y) ≡ VOA.conformalVector P.Y
      toAdd : (x y : S.State) →
        toState (VOA.GradedModule._+_ S.M x y)
        ≡ VOA.GradedModule._+_ P.M (toState x) (toState y)
      toScale : (k : S.Scalar) (x : S.State) →
        toState (VOA.GradedModule._·_ S.M k x)
        ≡ VOA.GradedModule._·_ P.M (toScalar k) (toState x)
      toMode : (x : S.State) (n : ℤ) (y : S.State) →
        toState (VOA.mode S.Y x n y)
        ≡ VOA.mode P.Y (toState x) n (toState y)
      toTranslation : (x : S.State) →
        toState (VOA.translation S.Y x)
        ≡ VOA.translation P.Y (toState x)

  open ExactFLMVOAIsomorphism public

  -- Inverse transport of the vertex operations is *derived*, not a new
  -- witness. This is the same concrete selected VOA, not a parallel clone.
  fromMode : (iso : ExactFLMVOAIsomorphism)
    (x : P.State) (n : ℤ) (y : P.State) →
    fromState iso (VOA.mode P.Y x n y)
    ≡ VOA.mode S.Y (fromState iso x) n (fromState iso y)
  fromMode iso x n y =
    trans
      (sym (cong (fromState iso)
        (cong₂ (λ a b → VOA.mode P.Y a n b)
          (toAfterFrom iso x) (toAfterFrom iso y))))
      (trans
        (sym (cong (fromState iso)
          (toMode iso (fromState iso x) n (fromState iso y))))
        (fromAfterTo iso
          (VOA.mode S.Y (fromState iso x) n (fromState iso y))))
    where
      cong₂ : ∀ {A B C : Set} (f : A → B → C)
        {a b : A} {c d : B} → a ≡ b → c ≡ d → f a c ≡ f b d
      cong₂ f refl refl = refl

  record ExactY443MonsterGroupIso
    {G H : Set}
    (gi : TM.GroupWithInverse G)
    (hi : TM.GroupWithInverse H) : Set where
    field
      toMonster : G → H
      fromMonster : H → G
      fromMonsterAfterTo : (g : G) → fromMonster (toMonster g) ≡ g
      toMonsterAfterFrom : (h : H) → toMonster (fromMonster h) ≡ h
      preservesIdentity :
        toMonster (Pair.identity gi) ≡ Pair.identity hi
      preservesProduct : (g k : G) →
        toMonster (Pair.multiply gi g k)
        ≡ Pair.multiply hi (toMonster g) (toMonster k)
      preservesInverse : (g : G) →
        toMonster (Pair.inverse gi g)
        ≡ Pair.inverse hi (toMonster g)

  open ExactY443MonsterGroupIso public

  module SourceActions
    {G H : Set}
    (gi : TM.GroupWithInverse G)
    (hi : TM.GroupWithInverse H)
    (groupIso : ExactY443MonsterGroupIso gi hi)
    (iso : ExactFLMVOAIsomorphism)
    (publishedAction : Action.ActualGroupAction {H} {P.State} hi)
    where

    transported : G → S.State → S.State
    transported g x =
      fromState iso
        (Action.act publishedAction (toMonster groupIso g) (toState iso x))

    transportedIdentity : (x : S.State) →
      transported (Pair.identity gi) x ≡ x
    transportedIdentity x =
      trans
        (cong (λ h → fromState iso
          (Action.act publishedAction h (toState iso x)))
          (preservesIdentity groupIso))
        (trans
          (cong (fromState iso)
            (Action.actsIdentity publishedAction (toState iso x)))
          (fromAfterTo iso x))

    transportedProduct : (g k : G) (x : S.State) →
      transported (Pair.multiply gi g k) x
      ≡ transported g (transported k x)
    transportedProduct g k x =
      trans
        (cong (λ h → fromState iso
          (Action.act publishedAction h (toState iso x)))
          (preservesProduct groupIso g k))
        (trans
          (cong (fromState iso)
            (Action.actsProduct publishedAction
              (toMonster groupIso g) (toMonster groupIso k)
              (toState iso x)))
          (cong (λ y → fromState iso
            (Action.act publishedAction (toMonster groupIso g) y))
            (sym (toAfterFrom iso
              (Action.act publishedAction
                (toMonster groupIso k) (toState iso x))))))

    transportedInverseLeft : (g : G) (x : S.State) →
      transported (Pair.inverse gi g) (transported g x) ≡ x
    transportedInverseLeft g x =
      trans
        (cong (λ h → fromState iso
          (Action.act publishedAction h
            (toState iso (transported g x))))
          (preservesInverse groupIso g))
        (trans
          (cong (λ y → fromState iso
            (Action.act publishedAction
              (Pair.inverse hi (toMonster groupIso g)) y))
            (toAfterFrom iso
              (Action.act publishedAction (toMonster groupIso g)
                (toState iso x))))
          (trans
            (cong (fromState iso)
              (Action.actsInverseLeft publishedAction
                (toMonster groupIso g) (toState iso x)))
            (fromAfterTo iso x)))

    transportedInverseRight : (g : G) (x : S.State) →
      transported g (transported (Pair.inverse gi g) x) ≡ x
    transportedInverseRight g x =
      trans
        (cong (λ y → fromState iso
          (Action.act publishedAction (toMonster groupIso g) y))
          (toAfterFrom iso
            (Action.act publishedAction
              (toMonster groupIso (Pair.inverse gi g)) (toState iso x))))
        (trans
          (cong (λ h → fromState iso
            (Action.act publishedAction (toMonster groupIso g)
              (Action.act publishedAction h (toState iso x))))
            (preservesInverse groupIso g))
          (trans
            (cong (fromState iso)
              (Action.actsInverseRight publishedAction
                (toMonster groupIso g) (toState iso x)))
            (fromAfterTo iso x)))

    actualSelectedAction : Action.ActualGroupAction {G} {S.State} gi
    actualSelectedAction = record
      { Action.act = transported
      ; Action.actsIdentity = transportedIdentity
      ; Action.actsProduct = transportedProduct
      ; Action.actsInverseLeft = transportedInverseLeft
      ; Action.actsInverseRight = transportedInverseRight
      }

    -- This is the exact computable comparison on two JMD source generators.
    -- With an independently selected preexisting action, we must test
    -- these equations on the same selected state, not just compare traces.
    agreementOn : (preexisting : Action.ActualGroupAction {G} {S.State} gi)
      (g : G) → Set
    agreementOn preexisting g =
      (x : S.State) →
      Action.act preexisting g x ≡ transported g x
