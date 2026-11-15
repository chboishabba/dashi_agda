module DASHI.Moonshine.Y443FLMFiniteBasisUVEndcapExact where

------------------------------------------------------------------------
-- U/V FINITE BASIS ENDGAME, NO REPEATED INFINITE ACTION OBLIGATIONS
--
-- The selected actual weight-two Griess algebra must have an inhabited
-- SPANNING family with 196884 genuine vectors. Given two genuine
-- VOA actions and exactly two source-generator comparisons on that basis,
-- this module constructs their equality for EVERY selected Vnatural state
-- and EVERY original Y443 group element.
--
-- Avoids the previous redundant field requiring the same u/v equality
-- on all weight-two states in addition to the finite basis proof.
-- Does not manufacture basis vectors, actual Monster matrices or FLM.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Fin.Base using (Fin)

import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as JMD
import DASHI.Moonshine.Y443FLMWeightTwoOnlyUVExact as UV
import DASHI.Moonshine.Y443FLMWeightTwoBasisUVExact as Basis

module Selected
  {G H : Set}
  (jmd : JMD.PresentedY443VNaturalSource G)
  (canonicalFLM : VOA.VertexOperatorAlgebra)
  (canonicalMonsterGroup : TM.GroupWithInverse H) where

  module T = UV.Selected jmd canonicalFLM canonicalMonsterGroup
  module B = Basis.Selected T.S.actualSelectedVOA

  module WithCanonical
    (canonical : T.S.CanonicalFLMReference)
    (griess : B.A.ConcreteGriessProduct) where

    module W = T.WithCanonical canonical
    module F = B.WithGriess griess

    record ActualFiniteBasisUVSource : Setω where
      field
        sourceOperators : W.TwoGeneratorVOAOperators
        sourceActionLaws : W.ExistingActionGroupLaws
        actualGriessSpan : F.ActualWeightTwoSpan

        -- Exactly two finite vector-family comparisons.
        originalUOnBasis :
          (i : Fin 196884) →
          B.A.weightTwoAction (W.oldU sourceOperators)
            (F.basisState actualGriessSpan i)
          ≡ B.A.weightTwoAction (W.newU sourceOperators)
            (F.basisState actualGriessSpan i)
        originalVOnBasis :
          (i : Fin 196884) →
          B.A.weightTwoAction (W.oldV sourceOperators)
            (F.basisState actualGriessSpan i)
          ≡ B.A.weightTwoAction (W.newV sourceOperators)
            (F.basisState actualGriessSpan i)
    open ActualFiniteBasisUVSource public

    constructWeightTwoWitness :
      (source : ActualFiniteBasisUVSource) →
      W.TwoGeneratorVOAWitness
    constructWeightTwoWitness source = record
      { W.operators = sourceOperators source
      ; W.weightTwoU =
          F.agreementOnAllWeightTwo
            (actualGriessSpan source)
            (W.oldU (sourceOperators source))
            (W.newU (sourceOperators source))
            (originalUOnBasis source)
      ; W.weightTwoV =
          F.agreementOnAllWeightTwo
            (actualGriessSpan source)
            (W.oldV (sourceOperators source))
            (W.newV (sourceOperators source))
            (originalVOnBasis source)
      }

    wholeMonsterOriginalActionFromFiniteBasis :
      (source : ActualFiniteBasisUVSource) →
      (g : G) (x : B.A.State) →
      VOA.VOAGroupAction.act (JMD.action jmd) g x
      ≡ W.W.C.transported g x
    wholeMonsterOriginalActionFromFiniteBasis source =
      W.allGroupActionsAgreeFromWeightTwo
        (sourceActionLaws source)
        (constructWeightTwoWitness source)
