module DASHI.Moonshine.Base369AppraisalHeisenbergMonomialActionBidiExact where

------------------------------------------------------------------------
-- BASE369 APPRAISAL FIBRE -> FULL MONOMIAL HEISENBERG BASIS ACTION
--
-- The repository already owns the exact carrier chart
--
--   AppraisalFibrePoint <-> X6 = F3^6
--
-- and the transported cyclic translation action.  This owner adds the other
-- half of the standard Schrodinger/Weyl basis action without introducing a
-- fresh 729-carrier:
--
--   translation : moves the X6/appraisal basis label;
--   modulation  : keeps that label and changes its C3 phase exponent.
--
-- Thus the semantic appraisal coordinate now carries the same generator-level
-- monomial action as the finite Heisenberg model.  This still does NOT identify
-- that model action with the actual restricted MN3B representation; that is a
-- separate same-action receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Carrier
import DASHI.Moonshine.Base369HeisenbergTranslationGridObstructionExact as Translation
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3

------------------------------------------------------------------------
-- 1. Phase-aware basis carriers.
------------------------------------------------------------------------

record AppraisalMonomialBasis : Set where
  constructor appraisalMonomial
  field
    phaseExponent : Trit
    appraisalPoint : Geometry.AppraisalFibrePoint
open AppraisalMonomialBasis public

record ModelMonomialBasis : Set where
  constructor modelMonomial
  field
    modelPhaseExponent : Trit
    modelPosition : H.X6
open ModelMonomialBasis public

appraisalMonomialToModel : AppraisalMonomialBasis → ModelMonomialBasis
appraisalMonomialToModel (appraisalMonomial phase point) =
  modelMonomial phase (Carrier.appraisalFibreToX6 point)

modelMonomialToAppraisal : ModelMonomialBasis → AppraisalMonomialBasis
modelMonomialToAppraisal (modelMonomial phase position) =
  appraisalMonomial phase (Carrier.x6ToAppraisalFibre position)

appraisalMonomialRoundTrip :
  (state : AppraisalMonomialBasis) →
  modelMonomialToAppraisal (appraisalMonomialToModel state) ≡ state
appraisalMonomialRoundTrip (appraisalMonomial phase point)
  rewrite Carrier.appraisalFibreRoundTrip point = refl

modelMonomialRoundTrip :
  (state : ModelMonomialBasis) →
  appraisalMonomialToModel (modelMonomialToAppraisal state) ≡ state
modelMonomialRoundTrip (modelMonomial phase position)
  rewrite Carrier.x6RoundTrip position = refl

------------------------------------------------------------------------
-- 2. Translation generator action on the exact appraisal carrier.
------------------------------------------------------------------------

appraisalTranslation :
  H.Axis6 → AppraisalMonomialBasis → AppraisalMonomialBasis
appraisalTranslation axis (appraisalMonomial phase point) =
  appraisalMonomial phase (Translation.heisenbergTranslateFibre axis point)

modelTranslation : H.Axis6 → ModelMonomialBasis → ModelMonomialBasis
modelTranslation axis (modelMonomial phase position) =
  modelMonomial phase (H.translate axis position)

appraisalTranslationIntertwinesModel :
  (axis : H.Axis6) →
  (state : AppraisalMonomialBasis) →
  appraisalMonomialToModel (appraisalTranslation axis state)
  ≡ modelTranslation axis (appraisalMonomialToModel state)
appraisalTranslationIntertwinesModel axis (appraisalMonomial phase point)
  rewrite Translation.heisenbergTranslateIntertwinesByConstruction axis point = refl

------------------------------------------------------------------------
-- 3. Modulation generator action: same basis label, phase exponent changes.
------------------------------------------------------------------------

appraisalModulationExponent :
  H.Axis6 → AppraisalMonomialBasis → Trit
appraisalModulationExponent axis state =
  H.modulationExponent axis
    (Carrier.appraisalFibreToX6 (appraisalPoint state))

modelModulationExponent : H.Axis6 → ModelMonomialBasis → Trit
modelModulationExponent axis state =
  H.modulationExponent axis (modelPosition state)

appraisalModulation :
  H.Axis6 → AppraisalMonomialBasis → AppraisalMonomialBasis
appraisalModulation axis (appraisalMonomial phase point) =
  appraisalMonomial
    (H._+3_
      (H.modulationExponent axis (Carrier.appraisalFibreToX6 point))
      phase)
    point

modelModulation : H.Axis6 → ModelMonomialBasis → ModelMonomialBasis
modelModulation axis (modelMonomial phase position) =
  modelMonomial
    (H._+3_ (H.modulationExponent axis position) phase)
    position

appraisalModulationIntertwinesModel :
  (axis : H.Axis6) →
  (state : AppraisalMonomialBasis) →
  appraisalMonomialToModel (appraisalModulation axis state)
  ≡ modelModulation axis (appraisalMonomialToModel state)
appraisalModulationIntertwinesModel axis (appraisalMonomial phase point) = refl

------------------------------------------------------------------------
-- 4. Exact cyclotomic reading of the phase exponent.
------------------------------------------------------------------------

phaseAmplitude : Trit → C3.Cyclotomic3
phaseAmplitude = Schrodinger.phase

phaseZeroAmplitudeIsOne : phaseAmplitude zer ≡ C3.one
phaseZeroAmplitudeIsOne = refl

phasePositiveAmplitudeIsZeta : phaseAmplitude pos ≡ C3.zeta
phasePositiveAmplitudeIsZeta = refl

phaseNegativeAmplitudeIsZetaSquared : phaseAmplitude neg ≡ C3.zetaSquared
phaseNegativeAmplitudeIsZetaSquared = refl

appraisalAmplitude : AppraisalMonomialBasis → C3.Cyclotomic3
appraisalAmplitude state = phaseAmplitude (phaseExponent state)

------------------------------------------------------------------------
-- 5. All 36 generator Weyl exponent relations transport to appraisal states.
------------------------------------------------------------------------

appraisalGeneratorWeylExponent :
  (dual translationAxis : H.Axis6) →
  (state : AppraisalMonomialBasis) →
  appraisalModulationExponent dual (appraisalTranslation translationAxis state)
  ≡ H._+3_
      (H.kronecker dual translationAxis)
      (appraisalModulationExponent dual state)
appraisalGeneratorWeylExponent dual translationAxis
  (appraisalMonomial phase point)
  rewrite Translation.heisenbergTranslateIntertwinesByConstruction
            translationAxis point =
  H.generatorWeylExponent
    dual translationAxis (Carrier.appraisalFibreToX6 point)

------------------------------------------------------------------------
-- 6. Boundary: model-side semantic action is now generated; actual restricted
--    representation identification remains the scientific payment.
------------------------------------------------------------------------

record AppraisalHeisenbergMonomialActionBoundary : Set where
  constructor appraisal-heisenberg-monomial-action-boundary
  field
    literalAppraisalCarrierReused : Bool
    appraisalX6BijectionReused : Bool
    translationActionIntertwined : Bool
    modulationPhaseActionIntertwined : Bool
    exactOneZetaZetaSquaredAmplitudeReused : Bool
    allThirtySixWeylExponentRelationsTransported : Bool
    nativeNonperiodicPathActionClaimed : Bool
    actualRestrictedMN3BActionIdentified : Bool
    cardinalityAloneUsedAsActionProof : Bool

canonicalAppraisalHeisenbergMonomialActionBoundary :
  AppraisalHeisenbergMonomialActionBoundary
canonicalAppraisalHeisenbergMonomialActionBoundary =
  appraisal-heisenberg-monomial-action-boundary
    true true true true true true false false false
