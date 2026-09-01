module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound6Exact where

------------------------------------------------------------------------
-- ROUND 6 BIDI SEARCH: THE 729 APPRAISAL ACTION IS DOWNSTREAM OF ZETA
-- RECOGNITION, NOT AN INDEPENDENT REPRESENTATION DISCOVERY PROBLEM.
--
-- Two existing facts are now composed explicitly:
--
--   AppraisalFibrePoint <-> X6
--   ActualZetaSectorRecognition : ActualSector <-> X6 x Fin 90.
--
-- Therefore, after one actual zeta recognition is recovered, fixing any
-- multiplicity coordinate gives an actual 729-state slice whose translation
-- and modulation observers already intertwine with the Base369 appraisal
-- coordinate.  Round 5's repo-native VOA action search remains the upstream
-- scientific target.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound5Exact as R5
import DASHI.Moonshine.Base369AppraisalHeisenbergMonomialActionBidiExact as Monomial
import DASHI.Moonshine.Base369Monster3BActualMultiplicitySliceAppraisalBidiExact as Slice

------------------------------------------------------------------------
-- 1. Round-6 leaves.
------------------------------------------------------------------------

data Round6Leaf : Set where
  appraisalX6CarrierChart : Round6Leaf
  appraisalMonomialHeisenbergAction : Round6Leaf
  actualVOAThreeBPhaseReceipts : Round6Leaf
  actualZetaRecognitionOnLiteralVOA : Round6Leaf
  separateActual729CarrierIdentification : Round6Leaf
  actual729AppraisalSlices : Round6Leaf
  actualFin90InertiaAction : Round6Leaf
  sameActionTwelveSeventyEight : Round6Leaf
  actualFiftyThreeResidualAction : Round6Leaf
  nestedLocalGlobalUnitBridge : Round6Leaf

data LeafState : Set where
  owned generated live pruned downstream parallel : LeafState

leafState : Round6Leaf → LeafState
leafState appraisalX6CarrierChart = owned
leafState appraisalMonomialHeisenbergAction = generated
leafState actualVOAThreeBPhaseReceipts = live
leafState actualZetaRecognitionOnLiteralVOA = live
leafState separateActual729CarrierIdentification = pruned
leafState actual729AppraisalSlices = downstream
leafState actualFin90InertiaAction = downstream
leafState sameActionTwelveSeventyEight = downstream
leafState actualFiftyThreeResidualAction = parallel
leafState nestedLocalGlobalUnitBridge = parallel

appraisalMonomialActionIsGenerated :
  leafState appraisalMonomialHeisenbergAction ≡ generated
appraisalMonomialActionIsGenerated = refl

separate729IdentificationIsPruned :
  leafState separateActual729CarrierIdentification ≡ pruned
separate729IdentificationIsPruned = refl

actual729SlicesWaitOnlyForZetaRecognition :
  leafState actual729AppraisalSlices ≡ downstream
actual729SlicesWaitOnlyForZetaRecognition = refl

------------------------------------------------------------------------
-- 2. The strongest model-side action facts are already generated.
------------------------------------------------------------------------

modelSideTranslationIntertwined : Bool
modelSideTranslationIntertwined =
  Monomial.AppraisalHeisenbergMonomialActionBoundary.translationActionIntertwined
    Monomial.canonicalAppraisalHeisenbergMonomialActionBoundary

modelSideModulationIntertwined : Bool
modelSideModulationIntertwined =
  Monomial.AppraisalHeisenbergMonomialActionBoundary.modulationPhaseActionIntertwined
    Monomial.canonicalAppraisalHeisenbergMonomialActionBoundary

modelSideWeylRelationsTransported : Bool
modelSideWeylRelationsTransported =
  Monomial.AppraisalHeisenbergMonomialActionBoundary.allThirtySixWeylExponentRelationsTransported
    Monomial.canonicalAppraisalHeisenbergMonomialActionBoundary

modelSideTranslationIntertwinedIsTrue : modelSideTranslationIntertwined ≡ true
modelSideTranslationIntertwinedIsTrue = refl

modelSideModulationIntertwinedIsTrue : modelSideModulationIntertwined ≡ true
modelSideModulationIntertwinedIsTrue = refl

modelSideWeylRelationsTransportedIsTrue : modelSideWeylRelationsTransported ≡ true
modelSideWeylRelationsTransportedIsTrue = refl

------------------------------------------------------------------------
-- 3. Round-5 upstream frontier remains the actual VOA/3B recognition seam.
------------------------------------------------------------------------

round5VOAActionSurfaceAlreadyOwned :
  R5.leafState R5.repoNativeVOAActionSurface ≡ R5.owned
round5VOAActionSurfaceAlreadyOwned = refl

round5SelectedThreeBReceiptsStillLive :
  R5.leafState R5.selectedThreeBCentralElementReceipts ≡ R5.live
round5SelectedThreeBReceiptsStillLive = refl

round5LiteralZetaRecognitionStillLive :
  R5.leafState R5.recognitionOnLiteralVOAZetaEigenspace ≡ R5.live
round5LiteralZetaRecognitionStillLive = refl

------------------------------------------------------------------------
-- 4. Search consequence.
------------------------------------------------------------------------

highestAlphaRound6Leaf : Round6Leaf
highestAlphaRound6Leaf = actualZetaRecognitionOnLiteralVOA

highestAlphaRound6LeafIsLive :
  leafState highestAlphaRound6Leaf ≡ live
highestAlphaRound6LeafIsLive = refl

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record Round6Boundary : Set where
  constructor round6-boundary
  field
    appraisalX6ChartAlreadyOwned : Bool
    appraisalFullMonomialGeneratorActionGenerated : Bool
    actualZetaRecognitionStillScientific : Bool
    actual729BridgeIndependentAfterZetaRecognition : Bool
    fixedFin90SliceGivesActual729Evaluation : Bool
    actualTranslationOnSliceIntertwinesAppraisal : Bool
    actualModulationObserverOnSliceIntertwinesAppraisal : Bool
    fin90InertiaStillDownstream : Bool
    twelveSeventyEightStillDownstream : Bool
    fiftyThreeActionStillParallel : Bool
    nestedUnitBridgeStillParallel : Bool

canonicalRound6Boundary : Round6Boundary
canonicalRound6Boundary =
  round6-boundary
    true true true false true true true true true true true
