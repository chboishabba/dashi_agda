module DASHI.Moonshine.Y443FLMCanonicalReferenceFromQuotientExact where

------------------------------------------------------------------------
-- COMPOSE ALL HONEST EXTERNAL SOURCE AUTHORITY AT THE ACTUAL SELECTED VOA.
--
-- The published FLM VOA and its Monster action must be actual sources;
-- the selected VN object must have an honest all-mode isomorphism to FLM;
-- original Y443 group G and canonical Monster H must each be shown to be
-- isomorphic to the SAME true 80-relator quotient Q.
--
-- This *constructs* CanonicalFLMReference, eliminating its generic
-- independently supplied group-iso field, by exact source group composition.
-- No fictional FLM or Ivanov witness is introduced.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (ℤ)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as JMD
import DASHI.Moonshine.Y443FLMConcreteSameObjectActionClosureExact as Closure
import DASHI.Moonshine.Y443PublishedQuotientIsoCompositionExact as Quotient
import DASHI.Moonshine.Y443TwoGeneratorSameVOAActionExact as Actions

module Selected {G H Q : Set}
  (jmd : JMD.PresentedY443VNaturalSource G)
  (publishedFLM : VOA.VertexOperatorAlgebra)
  (publishedMonsterGroup : TM.GroupWithInverse H)
  (actualY443QuotientGroup : TM.GroupWithInverse Q) where

  module S = Closure.Selected jmd publishedFLM publishedMonsterGroup
  module QIso = Quotient.Selected S.actualSelectedVOA
    actualY443QuotientGroup (JMD.groupWithInverse jmd) publishedMonsterGroup

  record SourceAuthority : Setω where
    field
      -- Real selected-to-canonical VOA map, not a grade-count match.
      originalVOAEqualsFLM : S.T.ExactFLMVOAIsomorphism
      -- Actual published 80-word quotient attached to both groups.
      bothGroupsAreSameMonsterQuotient : QIso.SamePublishedQuotient
      -- Genuine canonical group action, not an abstract Set declaration.
      actualPublishedMonsterAction :
        Actions.ActualGroupAction
          {H} {S.T.P.State} publishedMonsterGroup

      -- Genuine FLM VOA automorphism laws, not merely group actions.
      publishedVacuum : (h : H) →
        Actions.act actualPublishedMonsterAction h
          (VOA.vacuum S.T.P.Y)
        ≡ VOA.vacuum S.T.P.Y
      publishedConformal : (h : H) →
        Actions.act actualPublishedMonsterAction h
          (VOA.conformalVector S.T.P.Y)
        ≡ VOA.conformalVector S.T.P.Y
      publishedMode : (h : H)
        (x : S.T.P.State) (n : ℤ) (y : S.T.P.State) →
        Actions.act actualPublishedMonsterAction h
          (VOA.mode S.T.P.Y x n y)
        ≡ VOA.mode S.T.P.Y
          (Actions.act actualPublishedMonsterAction h x) n
          (Actions.act actualPublishedMonsterAction h y)
      publishedTranslation : (h : H) (x : S.T.P.State) →
        Actions.act actualPublishedMonsterAction h
          (VOA.translation S.T.P.Y x)
        ≡ VOA.translation S.T.P.Y
          (Actions.act actualPublishedMonsterAction h x)
  open SourceAuthority public

  assembleCanonicalReference :
    SourceAuthority → S.CanonicalFLMReference
  assembleCanonicalReference evidence = record
    { S.selectedIsCanonicalVOA = originalVOAEqualsFLM evidence
    ; S.y443IsCanonicalMonster =
        QIso.composedMonsterIsomorphism
          (bothGroupsAreSameMonsterQuotient evidence)
    ; S.publishedMonsterActs = actualPublishedMonsterAction evidence
    }


  module WithSource (source : SourceAuthority) where
    module C = S.T.SourceActions
      (JMD.groupWithInverse jmd)
      publishedMonsterGroup
      (QIso.composedMonsterIsomorphism
        (bothGroupsAreSameMonsterQuotient source))
      (originalVOAEqualsFLM source)
      (actualPublishedMonsterAction source)

    actualPublishedVOAAutomorphismLaws : C.PublishedActionVOALaws
    actualPublishedVOAAutomorphismLaws = record
      { C.preservesVacuum = publishedVacuum source
      ; C.preservesConformal = publishedConformal source
      ; C.preservesMode = publishedMode source
      ; C.preservesTranslation = publishedTranslation source
      }

    realSelectedTransportedModePreserved :
      (g : G) (x : S.T.S.State) (n : ℤ) (y : S.T.S.State) →
      C.transported g (VOA.mode S.T.S.Y x n y)
      ≡ VOA.mode S.T.S.Y
          (C.transported g x) n (C.transported g y)
    realSelectedTransportedModePreserved =
      C.transportedPreservesMode actualPublishedVOAAutomorphismLaws
