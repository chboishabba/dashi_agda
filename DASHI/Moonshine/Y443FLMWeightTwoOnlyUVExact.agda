module DASHI.Moonshine.Y443FLMWeightTwoOnlyUVExact where

-- Strongest selected-action reduction:
-- agree only on the actual weight-two generating carrier for JMD u,v.
-- Existing weight-two generation -> u/v agree on EVERY state;
-- existing JMD word cover -> EVERY group element agrees on EVERY state.
-- No canonical FLM model is fabricated and no C3/369 chart is assumed.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Y443FLMGriessFullAutSelectedVOAExact as FLM
import DASHI.Moonshine.Y443FLMConcreteSameObjectActionClosureExact as Closure
import DASHI.Moonshine.Y443TwoGeneratorSameVOAActionExact as GroupAction
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as JMD
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair

sym : ∀ {X : Set} {a b : X} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

module Selected
  {G H : Set}
  (jmd : JMD.PresentedY443VNaturalSource G)
  (canonicalFLM : VOA.VertexOperatorAlgebra)
  (canonicalMonsterGroup : TM.GroupWithInverse H) where

  module S = Closure.Selected jmd canonicalFLM canonicalMonsterGroup
  module A = FLM.Selected S.actualSelectedVOA

  module WithCanonical
    (canonical : S.CanonicalFLMReference) where

    module W = S.WithCanonical canonical

    record TwoGeneratorVOAWitness : Setω where
      field
        generation : A.WeightTwoGeneration
        oldU oldV newU newV : A.SelectedVOAAutomorphism

        oldURealises :
          (x : A.State) →
          A.action oldU x ≡
          VOA.VOAGroupAction.act (JMD.action jmd) (Pair.u S.originalWeld) x
        oldVRealises :
          (x : A.State) →
          A.action oldV x ≡
          VOA.VOAGroupAction.act (JMD.action jmd) (Pair.v S.originalWeld) x
        newURealises :
          (x : A.State) →
          A.action newU x ≡ W.C.transported (Pair.u S.originalWeld) x
        newVRealises :
          (x : A.State) →
          A.action newV x ≡ W.C.transported (Pair.v S.originalWeld) x

        -- Only two equality-of-linear-operators obligations, on grade 2.
        weightTwoU :
          (w : A.WeightTwo) →
          A.weightTwoAction oldU w ≡ A.weightTwoAction newU w
        weightTwoV :
          (w : A.WeightTwo) →
          A.weightTwoAction oldV w ≡ A.weightTwoAction newV w
    open TwoGeneratorVOAWitness public

    uAllStates :
      (e : TwoGeneratorVOAWitness) (x : A.State) →
      VOA.VOAGroupAction.act (JMD.action jmd) (Pair.u S.originalWeld) x
      ≡ W.C.transported (Pair.u S.originalWeld) x
    uAllStates e x =
      trans (sym (oldURealises e x))
        (trans
          (A.restrictionInjective
            (generation e) (oldU e) (newU e) (weightTwoU e) x)
          (newURealises e x))

    vAllStates :
      (e : TwoGeneratorVOAWitness) (x : A.State) →
      VOA.VOAGroupAction.act (JMD.action jmd) (Pair.v S.originalWeld) x
      ≡ W.C.transported (Pair.v S.originalWeld) x
    vAllStates e x =
      trans (sym (oldVRealises e x))
        (trans
          (A.restrictionInjective
            (generation e) (oldV e) (newV e) (weightTwoV e) x)
          (newVRealises e x))

    record ExistingActionGroupLaws : Setω where
      field
        oldAction :
          GroupAction.ActualGroupAction
            {G} {A.State} (JMD.groupWithInverse jmd)
        oldActionMatchesLiteral :
          (g : G) (x : A.State) →
          GroupAction.act oldAction g x
          ≡ VOA.VOAGroupAction.act (JMD.action jmd) g x
    open ExistingActionGroupLaws public

    allGroupActionsAgreeFromWeightTwo :
      (laws : ExistingActionGroupLaws)
      (e : TwoGeneratorVOAWitness)
      (g : G) (x : A.State) →
      VOA.VOAGroupAction.act (JMD.action jmd) g x
      ≡ W.C.transported g x
    allGroupActionsAgreeFromWeightTwo laws e g x =
      trans
        (sym (oldActionMatchesLiteral laws g x))
        (GroupAction.actionsAgreeEntireY443
          S.originalWeld
          (oldAction laws)
          W.C.actualSelectedAction
          (λ s → trans
            (oldActionMatchesLiteral laws (Pair.u S.originalWeld) s)
            (uAllStates e s))
          (λ s → trans
            (oldActionMatchesLiteral laws (Pair.v S.originalWeld) s)
            (vAllStates e s))
          g x)
