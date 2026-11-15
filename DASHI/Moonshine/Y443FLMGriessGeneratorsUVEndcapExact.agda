module DASHI.Moonshine.Y443FLMGriessGeneratorsUVEndcapExact where

------------------------------------------------------------------------
-- PREFERRED SHORT-CUT: two original JMD generator actions need agreement
-- only on any source-proved Griess algebra generating family.
--
-- Full VOA action then follows from:
--  Griess generators -> V2 (mode-one/add/scalar closure),
--  V2 -> Vnatural (weight-two generation and VOA mode closure),
--  u,v -> Y443 whole group (original JMD signed-word compiler).
--
-- No claim is made that a small generating family has been produced for
-- the ACTUAL FLM Griess algebra; the family must carry a genuine evaluator.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as JMD
import DASHI.Moonshine.Y443FLMWeightTwoOnlyUVExact as UV
import DASHI.Moonshine.Y443FLMGriessGeneratorUVExact as Gen

module Selected
  {G H : Set}
  (jmd : JMD.PresentedY443VNaturalSource G)
  (canonicalFLM : VOA.VertexOperatorAlgebra)
  (canonicalMonsterGroup : TM.GroupWithInverse H) where

  module T = UV.Selected jmd canonicalFLM canonicalMonsterGroup
  module B = Gen.Selected T.S.actualSelectedVOA

  module WithCanonical
    (canonical : T.S.CanonicalFLMReference)
    (griess : B.A.ConcreteGriessProduct)
    (Generator : Set)
    (seed : Generator → B.A.WeightTwo) where

    module W = T.WithCanonical canonical
    module F = B.WithGenerators griess Generator seed

    record RealGriessGeneratorsUVSource : Setω where
      field
        genuineGeneration : F.ActualGeneration
        sourceOperators : W.TwoGeneratorVOAOperators
        sourceActionLaws : W.ExistingActionGroupLaws
        -- These are the ONLY original u/v comparison obligations:
        originalUOnGenerator :
          (g : Generator) →
          B.A.weightTwoAction (W.oldU sourceOperators) (seed g)
          ≡ B.A.weightTwoAction (W.newU sourceOperators) (seed g)
        originalVOnGenerator :
          (g : Generator) →
          B.A.weightTwoAction (W.oldV sourceOperators) (seed g)
          ≡ B.A.weightTwoAction (W.newV sourceOperators) (seed g)
    open RealGriessGeneratorsUVSource public

    compileWeightTwoEquality :
      (src : RealGriessGeneratorsUVSource) →
      W.TwoGeneratorVOAWitness
    compileWeightTwoEquality src = record
      { W.operators = sourceOperators src
      ; W.weightTwoU =
          F.generatorAgreementIsWholeWeightTwo
            (genuineGeneration src)
            (W.oldU (sourceOperators src))
            (W.newU (sourceOperators src))
            (originalUOnGenerator src)
      ; W.weightTwoV =
          F.generatorAgreementIsWholeWeightTwo
            (genuineGeneration src)
            (W.oldV (sourceOperators src))
            (W.newV (sourceOperators src))
            (originalVOnGenerator src)
      }

    everyOriginalMonsterActionFromGriessSeeds :
      (source : RealGriessGeneratorsUVSource)
      (g : G) (x : B.A.State) →
      VOA.VOAGroupAction.act (JMD.action jmd) g x
      ≡ W.W.C.transported g x
    everyOriginalMonsterActionFromGriessSeeds source =
      W.allGroupActionsAgreeFromWeightTwo
        (sourceActionLaws source)
        (compileWeightTwoEquality source)
