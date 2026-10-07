{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstCurvatureChoiceRound523Exact where

------------------------------------------------------------------------
-- GOAL-1 C1 / ROUND523:
-- CHOOSE THE LITERAL CURVATURE OPERATOR FROM THE COMPLETED MARKED COMPOSITE
--
-- MarkedCurvatureCompositeFamily already constructs the completed local
-- operator and carries gauge/local proofs.  Therefore the equality
--
--   completed curvature composite = literal curvatureOperator
--
-- is a constructor choice on the preferred route.
--
-- The genuine source theorem remains production of the marked-source family
-- with its common Hilbert modulus and gauge/local semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature

record SourceFirstCurvatureChoice
    (C : Top.LiteralYangMillsCarriers) : Set₂ where
  field
    continuityScale :
      Top.CompactSimpleGroup C → Nuclear.ContinuityScale

    CompletedState :
      Top.CompactSimpleGroup C → Set

    family :
      ∀ group →
      Curvature.MarkedCurvatureCompositeFamily
        (Top.CurvaturePolynomial C)
        (Top.Position C)
        (continuityScale group)
        (CompletedState group)
        (Top.LocalOperator C)

open SourceFirstCurvatureChoice public

selectedCurvatureOperator :
  ∀ {C} →
  SourceFirstCurvatureChoice C →
  Top.CompactSimpleGroup C →
  Top.CurvaturePolynomial C →
  Top.LocalOperator C
selectedCurvatureOperator choice group =
  Curvature.localOperator (family choice group)

withSourceFirstCurvature :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S) →
  SourceFirstCurvatureChoice C →
  Top.LiteralYangMillsConstruction C S
withSourceFirstCurvature Y choice = record
  { Top.LiteralYangMillsConstruction.spacetime =
      Top.spacetime Y
  ; Top.LiteralYangMillsConstruction.finiteMeasure =
      Top.finiteMeasure Y
  ; Top.LiteralYangMillsConstruction.continuumMeasure =
      Top.continuumMeasure Y
  ; Top.LiteralYangMillsConstruction.schwinger =
      Top.schwinger Y
  ; Top.LiteralYangMillsConstruction.localObservable =
      Top.localObservable Y
  ; Top.LiteralYangMillsConstruction.curvatureOperator =
      selectedCurvatureOperator choice
  ; Top.LiteralYangMillsConstruction.opeCoefficient =
      Top.opeCoefficient Y
  ; Top.LiteralYangMillsConstruction.opeRemainder =
      Top.opeRemainder Y
  ; Top.LiteralYangMillsConstruction.stressTensor =
      Top.stressTensor Y
  ; Top.LiteralYangMillsConstruction.hilbertSpace =
      Top.hilbertSpace Y
  ; Top.LiteralYangMillsConstruction.hamiltonian =
      Top.hamiltonian Y
  ; Top.LiteralYangMillsConstruction.vacuum =
      Top.vacuum Y
  ; Top.LiteralYangMillsConstruction.massGap =
      Top.massGap Y
  }

completedCurvatureIsChosenLiteralOperator :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (choice : SourceFirstCurvatureChoice C)
    group polynomial →
  Curvature.localOperator (family choice group) polynomial
  ≡
  Top.curvatureOperator
    (withSourceFirstCurvature Y choice)
    group polynomial
completedCurvatureIsChosenLiteralOperator Y choice group polynomial = refl

selectedCurvatureGaugeInvariant :
  ∀ {C}
    (choice : SourceFirstCurvatureChoice C)
    group polynomial →
  Curvature.GaugeInvariant (family choice group)
    (selectedCurvatureOperator choice group polynomial)
selectedCurvatureGaugeInvariant choice group =
  Curvature.localOperatorGaugeInvariant (family choice group)

selectedCurvatureLocal :
  ∀ {C}
    (choice : SourceFirstCurvatureChoice C)
    group polynomial position →
  Curvature.LocalAt (family choice group)
    (selectedCurvatureOperator choice group polynomial)
    position
selectedCurvatureLocal choice group =
  Curvature.localOperatorLocal (family choice group)

round523SourceFirstCurvatureCompilerLevel : ProofLevel
round523SourceFirstCurvatureCompilerLevel = machineChecked

round523CurvatureLiteralEqualityLevel : ProofLevel
round523CurvatureLiteralEqualityLevel = machineChecked

literalRound523MarkedCurvatureFamilyLevel : ProofLevel
literalRound523MarkedCurvatureFamilyLevel =
  Curvature.literalMarkedCurvatureCompositeSourceLevel
