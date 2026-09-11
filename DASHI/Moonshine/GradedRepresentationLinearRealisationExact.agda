module DASHI.Moonshine.GradedRepresentationLinearRealisationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CALIBRATION
--
-- Jean-Pierre Serre, Linear Representations of Finite Groups.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Audrey Terras, Fourier Analysis on Finite Groups and Applications.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- `GradedRepresentation.FiniteDimensionalRepresentation` owns an abstract
-- carrier V, abstract endomorphisms End, an action G -> End and trace data.
-- `MonsterWeightTwoSemanticActionRealisationExact.EndomorphismEvaluation`
-- separately owns how those abstract End values evaluate on V.  Neither object
-- alone states that V is a vector carrier or that evaluated ends are linear.
--
-- This bridge adds exactly that missing payment without changing either source
-- API: a repo-native HilbertLift carrier is put in two-sided correspondence
-- with V, evaluated endomorphisms are transported across that correspondence,
-- and zero/add/scalar preservation are supplied explicitly.  The resulting
-- group action is then a `HilbertLorentzForcing.LinearAction`.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.MonsterWeightTwoSemanticActionRealisationExact as Eval

------------------------------------------------------------------------
-- Proof-bearing linear realisation.
------------------------------------------------------------------------

record LinearEndomorphismRealisation
    {G K : Set}
    (group : GR.Group G)
    (representation : GR.FiniteDimensionalRepresentation G K group) : Setω where
  field
    linearCarrier : Linear.HilbertLift
    endomorphismEvaluation : Eval.EndomorphismEvaluation group representation

    toRepresentationCarrier :
      Linear.Vector linearCarrier → GR.V representation
    fromRepresentationCarrier :
      GR.V representation → Linear.Vector linearCarrier

    representationAfterLinear :
      (v : Linear.Vector linearCarrier) →
      fromRepresentationCarrier (toRepresentationCarrier v) ≡ v

    linearAfterRepresentation :
      (v : GR.V representation) →
      toRepresentationCarrier (fromRepresentationCarrier v) ≡ v

    evaluatedEndPreservesZero :
      (end : GR.End representation) →
      fromRepresentationCarrier
        (Eval.applyEnd endomorphismEvaluation end
          (toRepresentationCarrier (Linear.zero linearCarrier)))
      ≡ Linear.zero linearCarrier

    evaluatedEndPreservesAddition :
      (end : GR.End representation) →
      (left right : Linear.Vector linearCarrier) →
      fromRepresentationCarrier
        (Eval.applyEnd endomorphismEvaluation end
          (toRepresentationCarrier
            (Linear._+_ linearCarrier left right)))
      ≡ Linear._+_ linearCarrier
          (fromRepresentationCarrier
            (Eval.applyEnd endomorphismEvaluation end
              (toRepresentationCarrier left)))
          (fromRepresentationCarrier
            (Eval.applyEnd endomorphismEvaluation end
              (toRepresentationCarrier right)))

    evaluatedEndPreservesScaling :
      (end : GR.End representation) →
      (scalar : Linear.Scalar linearCarrier) →
      (v : Linear.Vector linearCarrier) →
      fromRepresentationCarrier
        (Eval.applyEnd endomorphismEvaluation end
          (toRepresentationCarrier
            (Linear._·_ linearCarrier scalar v)))
      ≡ Linear._·_ linearCarrier scalar
          (fromRepresentationCarrier
            (Eval.applyEnd endomorphismEvaluation end
              (toRepresentationCarrier v)))

open LinearEndomorphismRealisation public

------------------------------------------------------------------------
-- Transport each abstract End to an actual map on the linear carrier.
------------------------------------------------------------------------

evaluatedEnd :
  ∀ {G K : Set}
    {group : GR.Group G}
    {representation : GR.FiniteDimensionalRepresentation G K group} →
  LinearEndomorphismRealisation group representation →
  GR.End representation →
  Linear.Vector (linearCarrier _) →
  Linear.Vector (linearCarrier _)
evaluatedEnd realisation end v =
  fromRepresentationCarrier realisation
    (Eval.applyEnd (endomorphismEvaluation realisation) end
      (toRepresentationCarrier realisation v))

------------------------------------------------------------------------
-- The represented group now acts on the actual linear carrier.
------------------------------------------------------------------------

groupLinearAction :
  ∀ {G K : Set}
    {group : GR.Group G}
    {representation : GR.FiniteDimensionalRepresentation G K group} →
  (realisation : LinearEndomorphismRealisation group representation) →
  Linear.LinearAction (linearCarrier realisation)
groupLinearAction {G} {representation = representation} realisation = record
  { Group = G
  ; act = λ g → evaluatedEnd realisation (GR.action representation g)
  }

------------------------------------------------------------------------
-- Source / classification coordinates are descriptive only.
------------------------------------------------------------------------

serreDOI : String
serreDOI = "10.1007/978-1-4684-9458-7"

terrasDOI : String
terrasDOI = "10.1017/CBO9780511626265"

groupRepresentationQID : String
groupRepresentationQID = "Q1055807"

representationCharacterQID : String
representationCharacterQID = "Q600043"

groupRepresentationDewey : String
groupRepresentationDewey = "512.22"

finiteGroupDewey : String
finiteGroupDewey = "512.23"

oeisRole : String
oeisRole = "not applicable: linear-endomorphism realisation is structure, not integer-sequence evidence"

------------------------------------------------------------------------
-- Boundary: this bridge is an interface, not a Monster inhabitant.
------------------------------------------------------------------------

record GradedRepresentationLinearRealisationBoundary : Set where
  constructor graded-representation-linear-realisation-boundary
  field
    abstractRepresentationActionAlreadyOwned : Bool
    endomorphismEvaluationAlreadyOwned : Bool
    linearCarrierRequiredSeparately : Bool
    evaluatedEndLinearityRequiredSeparately : Bool
    genericGroupLinearActionCompilerAvailable : Bool
    actualMonsterWeightTwoLinearRealisationInhabitedHere : Bool
open GradedRepresentationLinearRealisationBoundary public

canonicalGradedRepresentationLinearRealisationBoundary :
  GradedRepresentationLinearRealisationBoundary
canonicalGradedRepresentationLinearRealisationBoundary =
  graded-representation-linear-realisation-boundary
    true true true true true false
