module DASHI.Reasoning.Trialectic369SchrodingerMultiplicityHomCompilerExact where

------------------------------------------------------------------------
-- SCHRODINGER-FIXED ACTUAL LINEAR MULTIPLICITY HOM-SPACE COMPILER
--
-- DASHI CONTRIBUTION
--
-- Do not first construct an abstract ActualLinearMultiplicityHomSpace and then
-- separately prove that its H_zeta and W_zeta carriers are the desired ones.
--
-- Fix them definitionally:
--
--   H_zeta := SchrodingerFunction
--   W_zeta := Vector (zetaLinearCarrier producer)
--
-- The remaining source data is exactly the real representation-theoretic
-- payload:
--
--   S_zeta / EquivariantMap,
--   Hom <-> multiplicity carrier,
--   evaluation/recovery H_zeta x S_zeta <-> W_zeta,
--   cocycle-compensated action,
--   source-paid character and linear intertwiner receipts.
--
-- This compiles the existing ActualLinearMultiplicityHomSpace with both
-- carrier-binding equalities reducible to refl.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.Monster3BNormalizerCocycleCancellationExact as Cocycle
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta

------------------------------------------------------------------------
-- 1. Source data after fixing both representation carriers.
------------------------------------------------------------------------

record SchrodingerMultiplicityHomData
    (producer : LinearZeta.LinearSingleActionProducer)
    : Setω where
  field
    EquivariantMap : Set

    sameObjectLinearRepresentation :
      WrongType.LinearMultiplicityRepresentation

    homToMultiplicity :
      EquivariantMap →
      Linear.Vector
        (WrongType.linearCarrier sameObjectLinearRepresentation)

    multiplicityToHom :
      Linear.Vector
        (WrongType.linearCarrier sameObjectLinearRepresentation) →
      EquivariantMap

    multiplicityAfterHom :
      (f : EquivariantMap) →
      multiplicityToHom (homToMultiplicity f) ≡ f

    homAfterMultiplicity :
      (s :
        Linear.Vector
          (WrongType.linearCarrier sameObjectLinearRepresentation)) →
      homToMultiplicity (multiplicityToHom s) ≡ s

    evaluationMap :
      Schrodinger.SchrodingerFunction × EquivariantMap →
      Linear.Vector (LinearZeta.zetaLinearCarrier producer)

    evaluationInverse :
      Linear.Vector (LinearZeta.zetaLinearCarrier producer) →
      Schrodinger.SchrodingerFunction × EquivariantMap

    inverseAfterEvaluation :
      (tensor : Schrodinger.SchrodingerFunction × EquivariantMap) →
      evaluationInverse (evaluationMap tensor) ≡ tensor

    evaluationAfterInverse :
      (state : Linear.Vector (LinearZeta.zetaLinearCarrier producer)) →
      evaluationMap (evaluationInverse state) ≡ state

    cocycleCompensatedAction :
      Cocycle.CocycleCompensatedTensorAction

    cocycleMultiplicityIsSameLinearCarrier :
      Cocycle.Multiplicity cocycleCompensatedAction
      ≡
      Linear.Vector
        (WrongType.linearCarrier sameObjectLinearRepresentation)

    cocycleTensorIsSelectedLinearZetaCarrier :
      Cocycle.Tensor cocycleCompensatedAction
      ≡ Linear.Vector (LinearZeta.zetaLinearCarrier producer)

    sourcePaidCharacterOnSameMultiplicity : Set
    evaluationIsLinearIntertwiner : Set

open SchrodingerMultiplicityHomData public

------------------------------------------------------------------------
-- 2. Compile the canonical existing Hom-space owner.
------------------------------------------------------------------------

compileActualLinearMultiplicityHomSpace :
  (producer : LinearZeta.LinearSingleActionProducer) →
  SchrodingerMultiplicityHomData producer →
  Hom.ActualLinearMultiplicityHomSpace
compileActualLinearMultiplicityHomSpace producer data =
  record
    { HeisenbergCarrier =
        Schrodinger.SchrodingerFunction

    ; ChosenZetaCarrier =
        Linear.Vector (LinearZeta.zetaLinearCarrier producer)

    ; EquivariantMap =
        EquivariantMap data

    ; sameObjectLinearRepresentation =
        sameObjectLinearRepresentation data

    ; homToMultiplicity =
        homToMultiplicity data

    ; multiplicityToHom =
        multiplicityToHom data

    ; multiplicityAfterHom =
        multiplicityAfterHom data

    ; homAfterMultiplicity =
        homAfterMultiplicity data

    ; evaluationMap =
        evaluationMap data

    ; evaluationInverse =
        evaluationInverse data

    ; inverseAfterEvaluation =
        inverseAfterEvaluation data

    ; evaluationAfterInverse =
        evaluationAfterInverse data

    ; cocycleCompensatedAction =
        cocycleCompensatedAction data

    ; cocycleMultiplicityIsSameLinearCarrier =
        cocycleMultiplicityIsSameLinearCarrier data

    ; cocycleTensorIsChosenZetaCarrier =
        cocycleTensorIsSelectedLinearZetaCarrier data

    ; sourcePaidCharacterOnSameMultiplicity =
        sourcePaidCharacterOnSameMultiplicity data

    ; evaluationIsLinearIntertwiner =
        evaluationIsLinearIntertwiner data
    }

------------------------------------------------------------------------
-- 3. Carrier bindings are now definitional compiler output.
------------------------------------------------------------------------

compiledHeisenbergCarrierIsSchrodinger :
  (producer : LinearZeta.LinearSingleActionProducer) →
  (data : SchrodingerMultiplicityHomData producer) →
  Hom.HeisenbergCarrier
    (compileActualLinearMultiplicityHomSpace producer data)
  ≡ Schrodinger.SchrodingerFunction
compiledHeisenbergCarrierIsSchrodinger producer data = refl

compiledChosenZetaCarrierIsSelectedLinearWZeta :
  (producer : LinearZeta.LinearSingleActionProducer) →
  (data : SchrodingerMultiplicityHomData producer) →
  Hom.ChosenZetaCarrier
    (compileActualLinearMultiplicityHomSpace producer data)
  ≡ Linear.Vector (LinearZeta.zetaLinearCarrier producer)
compiledChosenZetaCarrierIsSelectedLinearWZeta producer data = refl

------------------------------------------------------------------------
-- 4. Firewalls.
------------------------------------------------------------------------

data DimensionNinetyCreatesHomData : Set where
data FiniteX6TimesFin90CreatesLinearEvaluation : Set where
data CharacterTwelvePlusSeventyEightCreatesHomData : Set where
data SameZetaScalarCreatesHomData : Set where

dimensionDoesNotCreateHomData :
  DimensionNinetyCreatesHomData → ⊥
dimensionDoesNotCreateHomData ()

finiteBasisDoesNotCreateLinearEvaluation :
  FiniteX6TimesFin90CreatesLinearEvaluation → ⊥
finiteBasisDoesNotCreateLinearEvaluation ()

characterDoesNotCreateHomData :
  CharacterTwelvePlusSeventyEightCreatesHomData → ⊥
characterDoesNotCreateHomData ()

sameScalarDoesNotCreateHomData :
  SameZetaScalarCreatesHomData → ⊥
sameScalarDoesNotCreateHomData ()

------------------------------------------------------------------------
-- 5. Machine-readable frontier.
------------------------------------------------------------------------

record Trialectic369SchrodingerMultiplicityHomCompilerBoundary : Set where
  constructor trialectic-369-schrodinger-multiplicity-hom-compiler-boundary
  field
    heisenbergCarrierFixedToSchrodinger : Bool
    chosenZetaCarrierFixedToSelectedLinearSector : Bool
    carrierBindingProofsAreDefinitional : Bool
    existingActualHomSpaceCompilerOwned : Bool
    abstractPostHocCarrierBindingsEliminated : Bool
    actualHomDataInhabitedHere : Bool
    actualEvaluationBidiInhabitedHere : Bool
    actualCocycleLiftInhabitedHere : Bool

canonicalTrialectic369SchrodingerMultiplicityHomCompilerBoundary :
  Trialectic369SchrodingerMultiplicityHomCompilerBoundary
canonicalTrialectic369SchrodingerMultiplicityHomCompilerBoundary =
  trialectic-369-schrodinger-multiplicity-hom-compiler-boundary
    true true true true true
    false false false
