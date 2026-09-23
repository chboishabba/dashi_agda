module DASHI.Law.SensibLawComparativeReadModelTypedMetadataRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Law.SensibLawComparativeReadModelTypedMetadataExact as M

boundary : M.ComparativeReadModelTypedMetadataBoundary
boundary = M.canonicalComparativeReadModelTypedMetadataBoundary

defeaterStillApplicability :
  M.layer M.pabaiDefeaterReadModelAnnotation ≡ Locus.applicabilityLayer
defeaterStillApplicability = refl

counterStillApplicability :
  M.layer M.pabaiCounterReadModelAnnotation ≡ Locus.applicabilityLayer
counterStillApplicability = refl

typedLayerStillCarried :
  M.typedChangeLayerCarriedIntoReadModel boundary ≡ true
typedLayerStillCarried = refl

justificationStillCarried :
  M.justificationReceiptCarriedIntoReadModel boundary ≡ true
justificationStillCarried = refl

uiStillCannotInferLayer :
  M.uiMayInferChangeLayerFromLabels boundary ≡ false
uiStillCannotInferLayer = refl

rendererStillCannotInferLayer :
  M.rendererMayInferChangeLayerFromGeometry boundary ≡ false
rendererStillCannotInferLayer = refl

missingJustificationStillCannotBeFilled :
  M.missingJustificationMayBeSilentlyFilled boundary ≡ false
missingJustificationStillCannotBeFilled = refl

presentationStillCreatesNoTruth :
  M.presentationCreatesClaimTruth boundary ≡ false
presentationStillCreatesNoTruth = refl
