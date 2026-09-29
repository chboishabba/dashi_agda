module DASHI.Physics.Foundations.FiniteWarpedSourceProducerBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Geometry.NonconstantWarpedLorentzianModel as Geometry
import DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel as Model
import DASHI.Physics.Closure.EinsteinEquationBidiResidualExact as Equation
import DASHI.Physics.Foundations.CoarseObservableFactorisationBidiExact as Coarse

------------------------------------------------------------------------
-- Literal finite action -> SAME finite tensor -> warped curvature.
-- No independent stress tensor is introduced: this producer evaluates the
-- existing selected matter action.  The three-valued SourceCoefficient
-- is only a normalised finite fixture, not SI-valued or quantum-renormalised.
------------------------------------------------------------------------

finiteActionSource : Model.MatterActionDensity → Model.EinsteinTensor4
finiteActionSource action a b = Model.varyMatterAction action a b

selectedAction : Model.MatterActionDensity
selectedAction = Model.matterActionAt Geometry.presentSlice

selectedFiniteSource : Model.EinsteinTensor4
selectedFiniteSource = finiteActionSource selectedAction

selectedSourceIsOriginal :
  (a b : Flat.Axis4) →
  selectedFiniteSource a b ≡ Model.computedMatterStress a b
selectedSourceIsOriginal a b = refl

sourceResidual :
  Model.EinsteinTensor4 →
  Flat.Axis4 → Flat.Axis4 → Model.SourceCoefficient
sourceResidual source a b =
  Model.addSource
    (Model.computedEinsteinTensor a b)
    (Model.negateSource (source a b))

-- Exact, exhaustive cancellation on this *specific* finite carrier.
zeroResidualForcesSameCoefficient :
  (geometry source : Model.SourceCoefficient) →
  Model.addSource geometry (Model.negateSource source)
    ≡ Model.zeroSource →
  geometry ≡ source
zeroResidualForcesSameCoefficient Model.negativeSource Model.negativeSource _ = refl
zeroResidualForcesSameCoefficient Model.negativeSource Model.zeroSource ()
zeroResidualForcesSameCoefficient Model.negativeSource Model.positiveSource ()
zeroResidualForcesSameCoefficient Model.zeroSource Model.negativeSource ()
zeroResidualForcesSameCoefficient Model.zeroSource Model.zeroSource _ = refl
zeroResidualForcesSameCoefficient Model.zeroSource Model.positiveSource ()
zeroResidualForcesSameCoefficient Model.positiveSource Model.negativeSource ()
zeroResidualForcesSameCoefficient Model.positiveSource Model.zeroSource ()
zeroResidualForcesSameCoefficient Model.positiveSource Model.positiveSource _ = refl

sameObjectFromAllSourceResiduals :
  (source : Model.EinsteinTensor4) →
  ((a b : Flat.Axis4) →
    sourceResidual source a b ≡ Model.zeroSource) →
  (a b : Flat.Axis4) →
  source a b ≡ Model.computedEinsteinTensor a b
sameObjectFromAllSourceResiduals source zero a b =
  sym (zeroResidualForcesSameCoefficient
         (Model.computedEinsteinTensor a b)
         (source a b)
         (zero a b))

selectedSourceResidualZero :
  (a b : Flat.Axis4) →
  sourceResidual selectedFiniteSource a b ≡ Model.zeroSource
selectedSourceResidualZero a b =
  Equation.normalizedEquationResidualPointwise a b

selectedSourceRecoveredSameObject :
  (a b : Flat.Axis4) →
  selectedFiniteSource a b ≡ Model.computedEinsteinTensor a b
selectedSourceRecoveredSameObject =
  sameObjectFromAllSourceResiduals
    selectedFiniteSource selectedSourceResidualZero

-- An actually different action fails the time-time residual. No source
-- promotion can follow from a type-compatible but unequal tensor.
emptyActionSource : Model.EinsteinTensor4
emptyActionSource = finiteActionSource Model.emptyActionDensity

emptySourceTimeResidualNonzero :
  sourceResidual emptyActionSource Flat.timeAxis Flat.timeAxis
    ≡ Model.positiveSource
emptySourceTimeResidualNonzero = refl

data FiniteSourceVerdict : Set where
  matchesSelectedWarpedGeometry : FiniteSourceVerdict
  failsSelectedWarpedGeometry : FiniteSourceVerdict

checkTimeSource : Model.EinsteinTensor4 → FiniteSourceVerdict
checkTimeSource source with
  Equation.sourceIsZero
    (sourceResidual source Flat.timeAxis Flat.timeAxis)
... | true = matchesSelectedWarpedGeometry
... | false = failsSelectedWarpedGeometry

selectedTimeSourceMatches :
  checkTimeSource selectedFiniteSource ≡ matchesSelectedWarpedGeometry
selectedTimeSourceMatches = refl

emptyTimeSourceFails :
  checkTimeSource emptyActionSource ≡ failsSelectedWarpedGeometry
emptyTimeSourceFails = refl

------------------------------------------------------------------------
-- Physical-state *image* carrier: the actual action at each time slice is
-- the one vacuum action. An arbitrary empty action has no preimage; making
-- the full MatterActionDensity the coarse carrier would falsely claim a
-- section. Use a precise image type to discharge the split projection.
------------------------------------------------------------------------

data SelectedActionImage : Set where
  selectedVacuum : SelectedActionImage

projectSliceAction : Geometry.TimeSlice → SelectedActionImage
projectSliceAction _ = selectedVacuum

selectedActionImageSplit :
  Coarse.SplitProjection Geometry.TimeSlice SelectedActionImage
selectedActionImageSplit = record
  { Coarse.SplitProjection.project = projectSliceAction
  ; Coarse.SplitProjection.section = λ _ → Geometry.presentSlice
  ; Coarse.SplitProjection.sectionRightInverse = λ { selectedVacuum → refl }
  }

sourceAtSlice :
  Geometry.TimeSlice → Flat.Axis4 → Flat.Axis4 →
  Model.SourceCoefficient
sourceAtSlice slice a b =
  finiteActionSource (Model.matterActionAt slice) a b

matterActionUniform :
  (slice : Geometry.TimeSlice) →
  Model.matterActionAt slice ≡ selectedAction
matterActionUniform Geometry.pastSlice = refl
matterActionUniform Geometry.presentSlice = refl
matterActionUniform Geometry.futureSlice = refl

sourceAtSliceUniform :
  (slice : Geometry.TimeSlice) (a b : Flat.Axis4) →
  sourceAtSlice slice a b ≡ selectedFiniteSource a b
sourceAtSliceUniform slice a b =
  cong (λ action → finiteActionSource action a b)
    (matterActionUniform slice)

sourceConsumerInvariant :
  (a b : Flat.Axis4) →
  Coarse.FibreInvariant selectedActionImageSplit
    (λ slice → sourceAtSlice slice a b)
sourceConsumerInvariant a b = record
  { Coarse.FibreInvariant.sameCoarseSameObservable =
      λ x y _ →
        trans (sourceAtSliceUniform x a b)
          (sym (sourceAtSliceUniform y a b))
  }

selectedStressFactorsThroughCoarseSlice :
  (slice : Geometry.TimeSlice) (a b : Flat.Axis4) →
  sourceAtSlice slice a b
  ≡ Coarse.coarseObservable selectedActionImageSplit
      (λ time → sourceAtSlice time a b)
      (projectSliceAction slice)
selectedStressFactorsThroughCoarseSlice slice a b =
  Coarse.factorisationFromFibreInvariance
    selectedActionImageSplit
    (λ time → sourceAtSlice time a b)
    (sourceConsumerInvariant a b)
    slice

-- This source is a model-level nonzero symmetric fixture with the earlier
-- finite continuity residual, NOT a selected YM expectation or
-- renormalised continuum conserved energy-momentum tensor.
finiteContinuityResidualStillZero :
  Model.continuityBianchiResidual ≡ Model.zeroSource
finiteContinuityResidualStillZero = Model.computedContractedBianchi
