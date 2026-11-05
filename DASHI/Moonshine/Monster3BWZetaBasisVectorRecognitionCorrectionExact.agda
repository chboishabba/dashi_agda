module DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact where

------------------------------------------------------------------------
-- W_zeta BASIS LABELS != THE FULL LITERAL VOA STATE CARRIER
--
-- The live Monster-3B frontier previously asked for a two-sided bijection
--
--   selected literal W_zeta  <->  X6 x Fin 90.
--
-- That target is too strong / wrong-typed when `selected literal W_zeta` means
-- the eigenspace inside `VertexOperatorAlgebraCore.GradedModule.Carrier`:
-- that carrier owns zero, addition and scalar multiplication and is therefore
-- the state/vector carrier.  By contrast `ZetaModelBasis = X6 x Fin 90` is
-- explicitly a finite BASIS-LABEL carrier.
--
-- The correct recognition programme has two separate layers:
--
--   (A) basis recognition
--       ActualBasisLabel <-> ZetaModelBasis,
--       with translation/modulation receipts on those basis labels and an
--       inclusion of basis vectors into the literal W_zeta state carrier;
--
--   (B) linear same-object recognition
--       H_zeta x S_zeta <-> W_zeta,
--       where S_zeta = Hom_E(H_zeta,W_zeta), using the already-existing
--       ActualLinearMultiplicityHomSpace / Schrodinger-H_zeta route.
--
-- A finite basis chart must not be promoted into a bijection between all
-- vectors and their basis labels.  Conversely, the linear Hom-space evaluation
-- does not by itself choose a Fin-90 basis of S_zeta.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom

------------------------------------------------------------------------
-- 1. Correct finite acquisition object: recognize BASIS LABELS, not every
--    vector in the literal eigenspace.
------------------------------------------------------------------------

record ActualZetaBasisRecognition (LiteralZetaSector : Set) : Set where
  field
    ActualBasisLabel : Set

    includeBasis : ActualBasisLabel → LiteralZetaSector

    toModelBasis : ActualBasisLabel → Model.ZetaModelBasis
    fromModelBasis : Model.ZetaModelBasis → ActualBasisLabel

    fromAfterTo :
      (basis : ActualBasisLabel) →
      fromModelBasis (toModelBasis basis) ≡ basis

    toAfterFrom :
      (basis : Model.ZetaModelBasis) →
      toModelBasis (fromModelBasis basis) ≡ basis

    actualTranslateBasis : H.Axis6 → ActualBasisLabel → ActualBasisLabel

    translationIntertwines :
      (axis : H.Axis6) →
      (basis : ActualBasisLabel) →
      toModelBasis (actualTranslateBasis axis basis)
      ≡ Model.translatedBasis axis (toModelBasis basis)

    actualModulationExponent : H.Axis6 → ActualBasisLabel → Trit

    modulationExponentIntertwines :
      (axis : H.Axis6) →
      (basis : ActualBasisLabel) →
      actualModulationExponent axis basis
      ≡ H.modulationExponent axis
          (Model.weightPosition (toModelBasis basis))

    -- The finite chart concerns actual basis vectors of the SAME literal
    -- eigenspace, not a detached combinatorial copy.
    basisInclusionIsRepresentationNative : Set

open ActualZetaBasisRecognition public

------------------------------------------------------------------------
-- 2. Multiplicity-basis recognition is a separate choice on the actual
--    linear Hom space S_zeta.  Dimension 90 / character isotypy is not such a
--    choice.
------------------------------------------------------------------------

record ActualMultiplicityBasisRecognition
    (homSpace : Hom.ActualLinearMultiplicityHomSpace) : Set where
  field
    MultiplicityBasisLabel : Set
    toFin90 : MultiplicityBasisLabel → Fin 90
    fromFin90 : Fin 90 → MultiplicityBasisLabel

    fromAfterTo :
      (label : MultiplicityBasisLabel) →
      fromFin90 (toFin90 label) ≡ label

    toAfterFrom :
      (index : Fin 90) →
      toFin90 (fromFin90 index) ≡ index

    includeMultiplicityBasis :
      MultiplicityBasisLabel → Hom.EquivariantMap homSpace

    multiplicityBasisIsLinearBasisOfHomSpace : Set
    normalizerActionOnMultiplicityBasisPaid : Set

open ActualMultiplicityBasisRecognition public

------------------------------------------------------------------------
-- 3. Correct combined target.
--
-- The existing linear Hom-space owner already carries the actual evaluation
-- and inverse H_zeta x S_zeta <-> W_zeta.  The new finite basis recognition
-- only supplies a compatible basis chart within that linear same-object weld.
------------------------------------------------------------------------

record WZetaBasisVectorRecognition
    (LiteralZetaSector : Set)
    (homSpace : Hom.ActualLinearMultiplicityHomSpace) : Set₁ where
  field
    basisRecognition : ActualZetaBasisRecognition LiteralZetaSector
    multiplicityBasisRecognition : ActualMultiplicityBasisRecognition homSpace

    homChosenZetaCarrierIsLiteralSector :
      Hom.ChosenZetaCarrier homSpace ≡ LiteralZetaSector

    schrodingerBasisToX6Paid : Set
    evaluationOfBasisTensorMatchesIncludedBasis : Set
    translationActionExtendsLinearlyFromBasis : Set
    modulationActionExtendsLinearlyFromBasis : Set

open WZetaBasisVectorRecognition public

------------------------------------------------------------------------
-- 4. Explicit wrong-type firewalls.
------------------------------------------------------------------------

data FiniteBasisLabelsAreAllVOAStates : Set where
data NinetyFoldIsotypyChoosesFin90Basis : Set where
data LinearHomEvaluationChoosesFiniteBasis : Set where
data Cardinality65610CreatesLiteralSectorBijection : Set where

finiteBasisLabelsDoNotBecomeAllVOAStates :
  FiniteBasisLabelsAreAllVOAStates → ⊥
finiteBasisLabelsDoNotBecomeAllVOAStates ()

isotypyDoesNotChooseFin90Basis :
  NinetyFoldIsotypyChoosesFin90Basis → ⊥
isotypyDoesNotChooseFin90Basis ()

linearEvaluationDoesNotChooseFiniteBasis :
  LinearHomEvaluationChoosesFiniteBasis → ⊥
linearEvaluationDoesNotChooseFiniteBasis ()

cardinalityDoesNotCreateLiteralSectorBijection :
  Cardinality65610CreatesLiteralSectorBijection → ⊥
cardinalityDoesNotCreateLiteralSectorBijection ()

------------------------------------------------------------------------
-- 5. Machine-readable correction boundary.
------------------------------------------------------------------------

record WZetaBasisVectorCorrectionBoundary : Set where
  constructor w-zeta-basis-vector-correction-boundary
  field
    literalVOACarrierHasLinearStateOperations : Bool
    literalVOAStateCarrierIsBasisLabelCarrier : Bool
    finiteX6Fin90IsBasisLabelSurface : Bool
    actualBasisRecognitionTargetTyped : Bool
    actualMultiplicityBasisTargetTyped : Bool
    linearHomEvaluationTargetReused : Bool
    wholeLiteralSectorBijectionToFiniteLabelsRequired : Bool
    ninetyFoldIsotypyChoosesMultiplicityBasis : Bool
    actualBasisRecognitionInhabitedHere : Bool
    actualLinearHomSameObjectPaidHere : Bool

open WZetaBasisVectorCorrectionBoundary public

canonicalBoundary : WZetaBasisVectorCorrectionBoundary
canonicalBoundary =
  w-zeta-basis-vector-correction-boundary
    true
    false
    true
    true
    true
    true
    false
    false
    false
    false
