module DASHI.Moonshine.Base369Monster3BRecognitionCompletionCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369

------------------------------------------------------------------------
-- BASE369 -> ACTUAL ZETA RECOGNITION COMPLETION COMPILER
--
-- The repository already owns an exact reversible carrier chart
--
--   Base369 appraisal fibre x Fin 90  <->  X6 x Fin 90 = ZetaModelBasis.
--
-- Existing owners only transport an ALREADY-PAID ActualZetaSectorRecognition
-- through that chart.  This owner proves the converse compiler: if the literal
-- actual zeta sector can be recognized directly in the native Base369 carrier,
-- with two-sided recovery plus translation/modulation intertwining, then the
-- exact existing Base369/model chart compiles those receipts into the stronger
-- repository ActualZetaSectorRecognition interface.
--
-- This changes the acquisition target, not its epistemic status.  No actual
-- Monster recognition inhabitant is constructed here.  Dimension 65610,
-- character isotypy, OEIS coordinates, QIDs and shared zeta notation do not
-- produce a Base369 recognition candidate.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Minimal native-Base369 acquisition object.
------------------------------------------------------------------------

record Base369RecognitionCandidate (ActualSector : Set) : Set where
  constructor base369-recognition-candidate
  field
    toBase369 : ActualSector → Base369.Base369MultiplicityBasis
    fromBase369 : Base369.Base369MultiplicityBasis → ActualSector

    fromAfterTo :
      (state : ActualSector) →
      fromBase369 (toBase369 state) ≡ state

    toAfterFrom :
      (basis : Base369.Base369MultiplicityBasis) →
      toBase369 (fromBase369 basis) ≡ basis

    actualTranslate : H.Axis6 → ActualSector → ActualSector

    translationIntertwines :
      (axis : H.Axis6) →
      (state : ActualSector) →
      toBase369 (actualTranslate axis state)
      ≡ Base369.translateBase369Multiplicity axis (toBase369 state)

    actualModulationExponent : H.Axis6 → ActualSector → Trit

    modulationExponentIntertwines :
      (axis : H.Axis6) →
      (state : ActualSector) →
      actualModulationExponent axis state
      ≡ Base369.base369ModulationExponent axis (proj₁ (toBase369 state))

open Base369RecognitionCandidate public

------------------------------------------------------------------------
-- 2. Existing Base369/model chart transports the operator receipts exactly.
------------------------------------------------------------------------

base369TranslationChartsToModel :
  (axis : H.Axis6) →
  (basis : Base369.Base369MultiplicityBasis) →
  Base369.base369ToModel
    (Base369.translateBase369Multiplicity axis basis)
  ≡ Model.translatedBasis axis (Base369.base369ToModel basis)
base369TranslationChartsToModel axis (fibre , multiplicity)
  rewrite Base369.base369TranslateChartsToHeisenberg axis fibre = refl

base369ModulationChartsToModel :
  (axis : H.Axis6) →
  (basis : Base369.Base369MultiplicityBasis) →
  Base369.base369ModulationExponent axis (proj₁ basis)
  ≡ H.modulationExponent axis
      (Model.weightPosition (Base369.base369ToModel basis))
base369ModulationChartsToModel axis (fibre , multiplicity) = refl

------------------------------------------------------------------------
-- 3. Reverse compiler into the stronger repository recognition interface.
------------------------------------------------------------------------

compileBase369Recognition :
  ∀ {ActualSector} →
  Base369RecognitionCandidate ActualSector →
  Actual.ActualZetaSectorRecognition ActualSector
compileBase369Recognition candidate =
  Actual.actual-zeta-sector-recognition
    (λ state → Base369.base369ToModel (toBase369 candidate state))
    (λ basis → fromBase369 candidate (Base369.modelToBase369 basis))
    (λ state →
      trans
        (cong (fromBase369 candidate)
          (Base369.base369ModelRoundTrip (toBase369 candidate state)))
        (fromAfterTo candidate state))
    (λ basis →
      trans
        (cong Base369.base369ToModel
          (toAfterFrom candidate (Base369.modelToBase369 basis)))
        (Base369.modelBase369RoundTrip basis))
    (actualTranslate candidate)
    (λ axis state →
      trans
        (cong Base369.base369ToModel
          (translationIntertwines candidate axis state))
        (base369TranslationChartsToModel axis (toBase369 candidate state)))
    (actualModulationExponent candidate)
    (λ axis state →
      trans
        (modulationExponentIntertwines candidate axis state)
        (base369ModulationChartsToModel axis (toBase369 candidate state)))

------------------------------------------------------------------------
-- 4. Any existing ActualZetaSectorRecognition yields a candidate again.
--    This records that Base369 coordinates are an equivalent acquisition
--    presentation once recognition is already available; it does not prove
--    record equality by function extensionality.
------------------------------------------------------------------------

candidateFromActualRecognition :
  ∀ {ActualSector} →
  Actual.ActualZetaSectorRecognition ActualSector →
  Base369RecognitionCandidate ActualSector
candidateFromActualRecognition recognition =
  base369-recognition-candidate
    (Base369.toBase369 (Base369.composeActualRecognitionWithBase369 recognition))
    (Base369.fromBase369 (Base369.composeActualRecognitionWithBase369 recognition))
    (Base369.fromAfterTo (Base369.composeActualRecognitionWithBase369 recognition))
    (Base369.toAfterFrom (Base369.composeActualRecognitionWithBase369 recognition))
    (Actual.actualTranslate recognition)
    (Base369.actualTranslationIntertwinesBase369 recognition)
    (Actual.actualModulationExponent recognition)
    (Base369.actualModulationExponentIntertwinesBase369 recognition)

------------------------------------------------------------------------
-- 5. WrongType / attribution firewalls.
------------------------------------------------------------------------

data DimensionCreatesBase369Candidate : Set where
data CharacterCreatesBase369Candidate : Set where
data OEISCreatesBase369Candidate : Set where
data QIDCreatesBase369Candidate : Set where
data CarrierBijectionCreatesOperatorIntertwining : Set where

dimensionDoesNotCreateBase369Candidate : DimensionCreatesBase369Candidate → ⊥
dimensionDoesNotCreateBase369Candidate ()

characterDoesNotCreateBase369Candidate : CharacterCreatesBase369Candidate → ⊥
characterDoesNotCreateBase369Candidate ()

oeisDoesNotCreateBase369Candidate : OEISCreatesBase369Candidate → ⊥
oeisDoesNotCreateBase369Candidate ()

qidDoesNotCreateBase369Candidate : QIDCreatesBase369Candidate → ⊥
qidDoesNotCreateBase369Candidate ()

carrierBijectionDoesNotCreateOperatorIntertwining :
  CarrierBijectionCreatesOperatorIntertwining → ⊥
carrierBijectionDoesNotCreateOperatorIntertwining ()

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

nextResidual : String
nextResidual =
  "acquire a Base369RecognitionCandidate for the exact selected literal W_zeta sector: a two-sided chart to appraisal-fibre x Fin90 plus six translation and six modulation-exponent intertwiners on that same selected action. The compiler here will then produce ActualZetaSectorRecognition automatically. The existing exact appraisal-fibre <-> X6 carrier chart discharges coordinate conversion only; it does not construct the actual-sector chart or operator receipts. OEIS/QID/dimension/character data remain non-promoting."

record Base369RecognitionCompletionBoundary : Set where
  constructor base369-recognition-completion-boundary
  field
    exactBase369ModelChartReused : Bool
    reverseRecognitionCompilerConstructed : Bool
    translationIntertwinerCompiled : Bool
    modulationIntertwinerCompiled : Bool
    actualBase369RecognitionCandidateInhabitedHere : Bool
    dimensionCreatesCandidate : Bool
    characterCreatesCandidate : Bool
    oeisCreatesCandidate : Bool
    nextResidual : String
open Base369RecognitionCompletionBoundary public

canonicalBase369RecognitionCompletionBoundary :
  Base369RecognitionCompletionBoundary
canonicalBase369RecognitionCompletionBoundary =
  base369-recognition-completion-boundary
    true true true true
    false false false false
    nextResidual
