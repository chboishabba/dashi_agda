module DASHI.Moonshine.Y443FLMDirectSameObjectCapstoneExact where

-- SOURCE-IDENTIFIED FLM / GRIESS / TITS / HUANG DIRECT ROUTE INTO Y443.
-- Reuse original JMD all-group 2-word compiler and SAME VN orbifold.
-- The genuine selected Griess product, FLM generation, Huang extension,
-- Tits automorphism identification and two JMD action agreements are
-- explicit inhabited-source obligations, not inferred from C3 traces.
-- Two-generator agreement suffices to prove SAME-VOA action for EVERY g.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as JMD
import DASHI.Moonshine.Y443FLMGriessFullAutSelectedVOAExact as FLM
import DASHI.Moonshine.Y443TwoGeneratorSameVOAActionExact as Compare

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

module SameObject {G : Set} (jmd : JMD.PresentedY443VNaturalSource G) where
  V : VOA.VertexOperatorAlgebra
  V = VN.VNaturalConstruction.Vnatural (JMD.construction jmd)

  module A = FLM.Selected V

  gi = JMD.groupWithInverse jmd

  weld : Pair.Y443VNaturalPairWeld G
  weld = JMD.compileSelectedWeld jmd

  State : Set
  State = A.State

  record PublishedFLMAndJMDSource : Setω where
    field
      genuineGriess : A.ConcreteGriessProduct
      flmWeightTwoGeneration : A.WeightTwoGeneration
      huangFullExtension : A.SelectedFLMExtension genuineGriess
      griessTitsMonster :
        A.SelectedMonsterGriessIdentification G genuineGriess

      originalAction : Compare.ActualGroupAction {G} {State} gi
      classicalAction : Compare.ActualGroupAction {G} {State} gi

      originalIsSameVOAAction : (g : G) (s : State) →
        Compare.act originalAction g s
        ≡ VOA.VOAGroupAction.act (JMD.action jmd) g s

      classicalIsPublishedExtension : (g : G) (s : State) →
        Compare.act classicalAction g s
        ≡ A.action
            (A.fullMonsterAction
              genuineGriess huangFullExtension griessTitsMonster g) s

      agreesOnJMDU : (s : State) →
        Compare.act originalAction (Pair.u weld) s
        ≡ Compare.act classicalAction (Pair.u weld) s

      agreesOnJMDV : (s : State) →
        Compare.act originalAction (Pair.v weld) s
        ≡ Compare.act classicalAction (Pair.v weld) s

  open PublishedFLMAndJMDSource public

  originalAndPublishedActionsAgreeEverywhere :
    (source : PublishedFLMAndJMDSource) (g : G) (s : State) →
    VOA.VOAGroupAction.act (JMD.action jmd) g s
    ≡ A.action
        (A.fullMonsterAction
          (genuineGriess source)
          (huangFullExtension source)
          (griessTitsMonster source)
          g) s
  originalAndPublishedActionsAgreeEverywhere source g s =
    trans (sym (originalIsSameVOAAction source g s))
      (trans
        (Compare.actionsAgreeEntireY443 weld
          (originalAction source)
          (classicalAction source)
          (agreesOnJMDU source)
          (agreesOnJMDV source) g s)
        (classicalIsPublishedExtension source g s))

  everySelectedVOAAutomorphismIsMonsterOnStates :
    (source : PublishedFLMAndJMDSource) →
    (a : A.SelectedVOAAutomorphism) →
    (s : State) →
    A.action
      (A.fullMonsterAction
        (genuineGriess source)
        (huangFullExtension source)
        (griessTitsMonster source)
        (A.recoverMonsterFromVOA
          (genuineGriess source)
          (griessTitsMonster source)
          a)) s
    ≡ A.action a s
  everySelectedVOAAutomorphismIsMonsterOnStates source a s =
    A.fullVOAAfterMonsterOnStates
      (genuineGriess source)
      (flmWeightTwoGeneration source)
      (huangFullExtension source)
      (griessTitsMonster source) a s

  everySelectedVOAAutomorphismIsOriginalY443Action :
    (source : PublishedFLMAndJMDSource) →
    (a : A.SelectedVOAAutomorphism) →
    (s : State) →
    VOA.VOAGroupAction.act (JMD.action jmd)
      (A.recoverMonsterFromVOA
        (genuineGriess source) (griessTitsMonster source) a)
      s
    ≡ A.action a s
  everySelectedVOAAutomorphismIsOriginalY443Action source a s =
    trans
      (originalAndPublishedActionsAgreeEverywhere source
        (A.recoverMonsterFromVOA
          (genuineGriess source) (griessTitsMonster source) a) s)
      (everySelectedVOAAutomorphismIsMonsterOnStates source a s)

  recoverOriginalMonsterElement :
    (source : PublishedFLMAndJMDSource) (g : G) →
    A.recoverMonsterFromVOA
      (genuineGriess source) (griessTitsMonster source)
      (A.fullMonsterAction
        (genuineGriess source)
        (huangFullExtension source)
        (griessTitsMonster source) g)
    ≡ g
  recoverOriginalMonsterElement source g =
    A.monsterAfterVOA
      (genuineGriess source)
      (huangFullExtension source)
      (griessTitsMonster source) g
