module DASHI.Reasoning.Trialectic369MultiplicityProjectionDescentCompilerExact where

------------------------------------------------------------------------
-- MULTIPLICITY-PROJECTION DESCENT COMPILER
--
-- DASHI CONTRIBUTION
--
-- ActualMonster3BActionRecognition already gives an exact same-object chart
--
--   X6 x Fin 90 <-> literal zeta sector.
--
-- Hence every actual central-inertia action can be transported back to an
-- action on X6 x Fin90 with no new scientific input.
--
-- For the trialectic outgoing residual we do NOT need the stronger historical
-- ActualMultiplicityInertiaAttachment, which also asks for an X6 action
-- independent of multiplicity.  We need only:
--
--   pi_90 (A(g)(x,m)) = A_90(g,m),
--
-- i.e. the multiplicity projection descends independently of X6.
--
-- From that single descent witness this module compiles:
--
--   * the literal actual Fin90 action;
--   * the canonical Fin10 x Fin9 action;
--   * a selected-Fine10 -> Sheet9 restriction whenever one fine fibre is
--     invariant.
--
-- Thus the outgoing scientific leaf is reduced to multiplicity-coordinate
-- descent plus the subsequent fine-fibre recognition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Multiplicity
import DASHI.Moonshine.Monster3BActualMultiplicityEvaluationFromRecognitionExact as Eval
import DASHI.Moonshine.Monster3BActualZetaPromotionPipelineExact as Pipeline
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Mixed
import DASHI.Reasoning.Trialectic369OutgoingSheet9MultiplicityRecognitionExact as Outgoing
import DASHI.Reasoning.Trialectic369OutgoingFineFrickeInvariantNoGoExact as FineFricke

------------------------------------------------------------------------
-- 1. Transport actual inertia to the exact X6 x Fin90 chart.
------------------------------------------------------------------------

ActualInertia :
  Action.ActualMonster3BActionRecognition ->
  Set
ActualInertia source =
  Inertia.CentralInertia (Action.normalizerAction source)

transportedActualProductAct :
  (source : Action.ActualMonster3BActionRecognition) ->
  ActualInertia source ->
  Multiplicity.ModelTensorBasis ->
  Multiplicity.ModelTensorBasis
transportedActualProductAct source inertia tensor =
  Eval.actualEvaluationInverse
    (Action.recognition source)
    (Pipeline.chosenInertiaAction
      (Action.actualPromotionPipeline source)
      inertia
      (Eval.actualEvaluationMap
        (Action.recognition source)
        tensor))

transportedActionReevaluatesToActualInertia :
  (source : Action.ActualMonster3BActionRecognition) ->
  (inertia : ActualInertia source) ->
  (tensor : Multiplicity.ModelTensorBasis) ->
  Eval.actualEvaluationMap
    (Action.recognition source)
    (transportedActualProductAct source inertia tensor)
  ≡
  Pipeline.chosenInertiaAction
    (Action.actualPromotionPipeline source)
    inertia
    (Eval.actualEvaluationMap
      (Action.recognition source)
      tensor)
transportedActionReevaluatesToActualInertia source inertia tensor =
  Eval.actualEvaluationRightInverse
    (Action.recognition source)
    (Pipeline.chosenInertiaAction
      (Action.actualPromotionPipeline source)
      inertia
      (Eval.actualEvaluationMap
        (Action.recognition source)
        tensor))

------------------------------------------------------------------------
-- 2. The one required descent datum.
------------------------------------------------------------------------

record MultiplicityProjectionDescent
    (source : Action.ActualMonster3BActionRecognition)
    : Set₁ where
  field
    multiplicityAct :
      ActualInertia source ->
      Fin 90 ->
      Fin 90

    multiplicityProjectionIntertwines :
      (inertia : ActualInertia source) ->
      (position : H.X6) ->
      (multiplicity : Fin 90) ->
      proj₂
        (transportedActualProductAct
          source inertia (position , multiplicity))
      ≡ multiplicityAct inertia multiplicity

open MultiplicityProjectionDescent public

actualMultiplicityCoordinateAfterInertia :
  (source : Action.ActualMonster3BActionRecognition) ->
  (descent : MultiplicityProjectionDescent source) ->
  (inertia : ActualInertia source) ->
  (position : H.X6) ->
  (multiplicity : Fin 90) ->
  Multiplicity.actualMultiplicityCoordinate
    (Action.recognition source)
    (Pipeline.chosenInertiaAction
      (Action.actualPromotionPipeline source)
      inertia
      (Eval.actualEvaluationMap
        (Action.recognition source)
        (position , multiplicity)))
  ≡ multiplicityAct descent inertia multiplicity
actualMultiplicityCoordinateAfterInertia
  source descent inertia position multiplicity =
  multiplicityProjectionIntertwines
    descent inertia position multiplicity

------------------------------------------------------------------------
-- 3. Canonical 10 x 9 action from multiplicity descent only.
------------------------------------------------------------------------

TenByNineSurface : Set
TenByNineSurface =
  Pointed.Fine10 × Pointed.SecondarySheet9

compiledTenByNineAct :
  (source : Action.ActualMonster3BActionRecognition) ->
  MultiplicityProjectionDescent source ->
  ActualInertia source ->
  TenByNineSurface ->
  TenByNineSurface
compiledTenByNineAct source descent inertia surface =
  Mixed.fin90ToTenByNine
    (multiplicityAct descent inertia
      (Mixed.tenByNineToFin90 surface))

compiledTenByNineIntertwines :
  (source : Action.ActualMonster3BActionRecognition) ->
  (descent : MultiplicityProjectionDescent source) ->
  (inertia : ActualInertia source) ->
  (multiplicity : Fin 90) ->
  Mixed.fin90ToTenByNine
    (multiplicityAct descent inertia multiplicity)
  ≡
  compiledTenByNineAct
    source descent inertia
    (Mixed.fin90ToTenByNine multiplicity)
compiledTenByNineIntertwines source descent inertia multiplicity
  rewrite Mixed.tenByNineAfterFin90 multiplicity = refl

------------------------------------------------------------------------
-- 4. Selected fine-fibre restriction directly from this weaker action.
------------------------------------------------------------------------

record SelectedFineFibreInvariant
    (source : Action.ActualMonster3BActionRecognition)
    (descent : MultiplicityProjectionDescent source)
    : Set₁ where
  field
    selectedFine : Pointed.Fine10

    selectedFinePreserved :
      (inertia : ActualInertia source) ->
      (sheet : Codec.Sheet9) ->
      proj₁
        (compiledTenByNineAct
          source descent inertia
          (Outgoing.embedSecondaryAt selectedFine sheet))
      ≡ selectedFine

open SelectedFineFibreInvariant public

compiledSheetAct :
  (source : Action.ActualMonster3BActionRecognition) ->
  (descent : MultiplicityProjectionDescent source) ->
  SelectedFineFibreInvariant source descent ->
  ActualInertia source ->
  Codec.Sheet9 ->
  Codec.Sheet9
compiledSheetAct source descent invariant inertia sheet =
  Outgoing.projectSecondary
    (compiledTenByNineAct
      source descent inertia
      (Outgoing.embedSecondaryAt
        (selectedFine invariant)
        sheet))

compiledActionStaysInSelectedFibre :
  (source : Action.ActualMonster3BActionRecognition) ->
  (descent : MultiplicityProjectionDescent source) ->
  (invariant : SelectedFineFibreInvariant source descent) ->
  (inertia : ActualInertia source) ->
  (sheet : Codec.Sheet9) ->
  compiledTenByNineAct
    source descent inertia
    (Outgoing.embedSecondaryAt
      (selectedFine invariant)
      sheet)
  ≡
  Outgoing.embedSecondaryAt
    (selectedFine invariant)
    (compiledSheetAct
      source descent invariant inertia sheet)
compiledActionStaysInSelectedFibre
  source descent invariant inertia sheet
  with compiledTenByNineAct
        source descent inertia
        (Outgoing.embedSecondaryAt
          (selectedFine invariant)
          sheet)
... | fine , secondary
  rewrite selectedFinePreserved invariant inertia sheet
        | Outgoing.secondaryCodecRoundTrip secondary = refl

------------------------------------------------------------------------
-- 4b. Conditional Fricke-like fine motion on the weaker path.
------------------------------------------------------------------------

record FineFrickeElement
    (source : Action.ActualMonster3BActionRecognition)
    (descent : MultiplicityProjectionDescent source)
    : Set₁ where
  field
    frickeInertia : ActualInertia source

    fineProjectionIsFiniteFricke :
      (fine : Pointed.Fine10) ->
      (sheet : Codec.Sheet9) ->
      proj₁
        (compiledTenByNineAct
          source descent frickeInertia
          (Outgoing.embedSecondaryAt fine sheet))
      ≡ FineFricke.fine10FiniteFricke fine

open FineFrickeElement public

fineFrickeRejectsSelectedFineInvariant :
  (source : Action.ActualMonster3BActionRecognition) ->
  (descent : MultiplicityProjectionDescent source) ->
  FineFrickeElement source descent ->
  SelectedFineFibreInvariant source descent ->
  ⊥
fineFrickeRejectsSelectedFineInvariant
  source descent element invariant =
  FineFricke.fine10FiniteFrickeNoFixedPoint
    (selectedFine invariant)
    fixed
  where
    zeroSheet : Codec.Sheet9
    zeroSheet =
      FineFricke.zeroOutgoingSheet

    fixed :
      FineFricke.fine10FiniteFricke
        (selectedFine invariant)
      ≡ selectedFine invariant
    fixed =
      trans
        (sym
          (fineProjectionIsFiniteFricke
            element
            (selectedFine invariant)
            zeroSheet))
        (selectedFinePreserved
          invariant
          (frickeInertia element)
          zeroSheet)

ModeBlock18 : Set
ModeBlock18 =
  Nonary.BinaryPhase × Codec.Sheet9

modeBlock18Count : Nat
modeBlock18Count = 2 * 9

modeBlock18CountIsEighteen :
  modeBlock18Count ≡ 18
modeBlock18CountIsEighteen = refl

fineAtModePhase :
  Nonary.ComplementMode5 ->
  Nonary.BinaryPhase ->
  Pointed.Fine10
fineAtModePhase mode phase =
  FineFricke.decimalToFine10
    (Nonary.decodeModePhase (mode , phase))

embedModeBlock18 :
  Nonary.ComplementMode5 ->
  ModeBlock18 ->
  TenByNineSurface
embedModeBlock18 mode (phase , sheet) =
  Outgoing.embedSecondaryAt
    (fineAtModePhase mode phase)
    sheet

fineFrickeAtModePhase :
  (mode : Nonary.ComplementMode5) ->
  (phase : Nonary.BinaryPhase) ->
  FineFricke.fine10FiniteFricke
    (fineAtModePhase mode phase)
  ≡ fineAtModePhase mode (Nonary.flipBinaryPhase phase)
fineFrickeAtModePhase Nonary.mode09 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode09 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode18 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode18 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode27 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode27 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode36 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode36 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode45 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode45 Nonary.counterPhase = refl

compiledFrickeModeBlock18Act :
  (source : Action.ActualMonster3BActionRecognition) ->
  (descent : MultiplicityProjectionDescent source) ->
  FineFrickeElement source descent ->
  Nonary.ComplementMode5 ->
  ModeBlock18 ->
  ModeBlock18
compiledFrickeModeBlock18Act
  source descent element mode (phase , sheet) =
  Nonary.flipBinaryPhase phase ,
  Outgoing.projectSecondary
    (compiledTenByNineAct
      source descent
      (frickeInertia element)
      (embedModeBlock18 mode (phase , sheet)))

compiledFrickeModeBlock18Intertwines :
  (source : Action.ActualMonster3BActionRecognition) ->
  (descent : MultiplicityProjectionDescent source) ->
  (element : FineFrickeElement source descent) ->
  (mode : Nonary.ComplementMode5) ->
  (state : ModeBlock18) ->
  compiledTenByNineAct
    source descent
    (frickeInertia element)
    (embedModeBlock18 mode state)
  ≡
  embedModeBlock18 mode
    (compiledFrickeModeBlock18Act
      source descent element mode state)
compiledFrickeModeBlock18Intertwines
  source descent element mode (phase , sheet)
  with compiledTenByNineAct
        source descent
        (frickeInertia element)
        (embedModeBlock18 mode (phase , sheet))
... | fine , secondary
  rewrite fineProjectionIsFiniteFricke
            element
            (fineAtModePhase mode phase)
            sheet
        | fineFrickeAtModePhase mode phase
        | Outgoing.secondaryCodecRoundTrip secondary = refl

------------------------------------------------------------------------
-- 5. Exact obstruction to multiplicity descent: dependence on X6.
------------------------------------------------------------------------

record MultiplicityCrossDependenceWitness
    (source : Action.ActualMonster3BActionRecognition)
    : Set where
  field
    inertia : ActualInertia source
    multiplicity : Fin 90
    leftPosition rightPosition : H.X6

    outputsDiffer :
      proj₂
        (transportedActualProductAct
          source inertia (leftPosition , multiplicity))
      ≢
      proj₂
        (transportedActualProductAct
          source inertia (rightPosition , multiplicity))

open MultiplicityCrossDependenceWitness public

crossDependenceRejectsMultiplicityDescent :
  (source : Action.ActualMonster3BActionRecognition) ->
  MultiplicityCrossDependenceWitness source ->
  MultiplicityProjectionDescent source ->
  ⊥
crossDependenceRejectsMultiplicityDescent source witness descent =
  outputsDiffer witness
    (trans
      (multiplicityProjectionIntertwines
        descent
        (inertia witness)
        (leftPosition witness)
        (multiplicity witness))
      (sym
        (multiplicityProjectionIntertwines
          descent
          (inertia witness)
          (rightPosition witness)
          (multiplicity witness))))

------------------------------------------------------------------------
-- 6. Frontier boundary.
------------------------------------------------------------------------

data MultiplicityProjectionDescentRecognizedHere : Set where
data SelectedFineFibreRecognizedHere : Set where

record Trialectic369MultiplicityProjectionDescentCompilerBoundary : Set where
  constructor trialectic-369-multiplicity-projection-descent-compiler-boundary
  field
    actualInertiaTransportedToX6TimesFin90 : Bool
    onlyMultiplicityProjectionDescentRequired : Bool
    independentX6ActionNotRequired : Bool
    canonicalTenByNineActionCompiled : Bool
    selectedFineSheetActionCompiled : Bool
    fineFrickeRejectsSelectedFineFibre : Bool
    frickeStableModeBlock18Compiled : Bool
    x6CrossDependenceRejectsMultiplicityDescent : Bool
    multiplicityProjectionDescentPaidHere : Bool
    selectedFineFibrePaidHere : Bool

canonicalTrialectic369MultiplicityProjectionDescentCompilerBoundary :
  Trialectic369MultiplicityProjectionDescentCompilerBoundary
canonicalTrialectic369MultiplicityProjectionDescentCompilerBoundary =
  trialectic-369-multiplicity-projection-descent-compiler-boundary
    true true true true true
    true true true
    false false
