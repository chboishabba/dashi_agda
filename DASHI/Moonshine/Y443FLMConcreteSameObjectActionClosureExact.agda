module DASHI.Moonshine.Y443FLMConcreteSameObjectActionClosureExact where

------------------------------------------------------------------------
-- TWO REMAINING GATES, JOINED TO THE *EXISTING* SELECTED Vnatural.
--
-- 1. Concrete VOA equivalence, with actual field/grade/state and ALL mode
--    operations preserved, transports the canonical FLM Monster action.
-- 2. Ivanov/Bray Y443 group equivalence with the canonical Monster group.
-- 3. The independently existing selected group action is compared with
--    this canonical transported action on precisely the JMD u,v elements.
--
-- Once paid, the old Y443 source-backed whole-group word covering theorem
-- derives equality of the actions on EVERY element and the selected grade-2
-- Griess representation. This is not a new action replacing the old one.
--
-- No Y443 word search, C3 trace, or BT prefix trie substitutes for the
-- supplied source group equivalence and structure-preserving VOA map.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as JMD
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443TwoGeneratorSameVOAActionExact as Act
import DASHI.Moonshine.Y443FLMConcreteVOAGroupTransportExact as Transport

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

module Selected
  {G H : Set}
  (jmd : JMD.PresentedY443VNaturalSource G)
  (canonicalFLM : VOA.VertexOperatorAlgebra)
  (canonicalMonsterGroup : TM.GroupWithInverse H)
  where

  actualSelectedVOA : VOA.VertexOperatorAlgebra
  actualSelectedVOA =
    VN.VNaturalConstruction.Vnatural (JMD.construction jmd)

  module T = Transport.Transport actualSelectedVOA canonicalFLM

  sourceGroup : TM.GroupWithInverse G
  sourceGroup = JMD.groupWithInverse jmd

  originalWeld : Pair.Y443VNaturalPairWeld G
  originalWeld = JMD.compileSelectedWeld jmd

  -- This is the ONLY input required for full canonical transport, followed
  -- by the two tests against any independently selected preexisting action.
  record CanonicalFLMReference : Setω where
    field
      selectedIsCanonicalVOA : T.ExactFLMVOAIsomorphism
      y443IsCanonicalMonster :
        T.ExactY443MonsterGroupIso sourceGroup canonicalMonsterGroup
      publishedMonsterActs :
        Act.ActualGroupAction
          {H} {T.P.State} canonicalMonsterGroup
  open CanonicalFLMReference public

  module WithCanonical
    (canonical : CanonicalFLMReference) where

    module C = T.SourceActions
      sourceGroup canonicalMonsterGroup
      (y443IsCanonicalMonster canonical)
      (selectedIsCanonicalVOA canonical)
      (publishedMonsterActs canonical)

    record OriginalActionAgreement : Setω where
      field
        -- The original VOAGroupAction only has Set-valued law declarations;
        -- the pointwise genuine group action is the required active receipt.
        originalSelectedAction :
          Act.ActualGroupAction {G} {T.S.State} sourceGroup
        actionIsExistingLiteral :
          (g : G) (x : T.S.State) →
          Act.act originalSelectedAction g x
          ≡ VOA.VOAGroupAction.act (JMD.action jmd) g x

        -- Exactly two equations on all states of the SAME selected VOA.
        originalU :
          C.agreementOn originalSelectedAction (Pair.u originalWeld)
        originalV :
          C.agreementOn originalSelectedAction (Pair.v originalWeld)
    open OriginalActionAgreement public

    originalEqualsCanonicalOnEveryElement :
      (agreement : OriginalActionAgreement) (g : G) (x : T.S.State) →
      VOA.VOAGroupAction.act (JMD.action jmd) g x
      ≡ C.transported g x
    originalEqualsCanonicalOnEveryElement agreement g x =
      trans
        (sym (actionIsExistingLiteral agreement g x))
        (Act.actionsAgreeEntireY443 originalWeld
          (originalSelectedAction agreement)
          C.actualSelectedAction
          (originalU agreement)
          (originalV agreement) g x)

    -- This explicitly witnesses the SAME actual grade-two carrier action,
    -- with the canonical source's grade-two inclusion, no numeric
    -- dimension-only promotion and no separate copy of the Griess action.
    gradeTwoOriginalActionIntertwinesCanonical :
      (agreement : OriginalActionAgreement)
      (g : G) (x : T.S.Grade 2) →
      T.toState (selectedIsCanonicalVOA canonical)
        (VOA.VOAGroupAction.act
          (JMD.action jmd) g (T.S.include 2 x))
      ≡
      Act.act (publishedMonsterActs canonical)
        (T.toMonster (y443IsCanonicalMonster canonical) g)
        (T.P.include 2
          (T.toGrade (selectedIsCanonicalVOA canonical) 2 x))
    gradeTwoOriginalActionIntertwinesCanonical agreement g x =
      trans
        (cong (T.toState (selectedIsCanonicalVOA canonical))
          (originalEqualsCanonicalOnEveryElement agreement
            g (T.S.include 2 x)))
        (trans
          (T.toAfterFrom (selectedIsCanonicalVOA canonical)
            (Act.act (publishedMonsterActs canonical)
              (T.toMonster (y443IsCanonicalMonster canonical) g)
              (T.toState (selectedIsCanonicalVOA canonical)
                (T.S.include 2 x))))
          (cong
            (Act.act (publishedMonsterActs canonical)
              (T.toMonster (y443IsCanonicalMonster canonical) g))
            (T.toIncludes (selectedIsCanonicalVOA canonical) 2 x)))
