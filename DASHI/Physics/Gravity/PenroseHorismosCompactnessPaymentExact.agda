module DASHI.Physics.Gravity.PenroseHorismosCompactnessPaymentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Gravity.CausalFutureHorismosNullGeneratorExact as Causal
import DASHI.Physics.Gravity.NullRaychaudhuriSachsFocusingExact as Focusing

record PenroseHorismosCompactnessBoundary : Set where
  field
    compactTrappedSurfaceCarrier : Bool
    compactTrappedSurfaceCarrierIsTrue : compactTrappedSurfaceCarrier ≡ true
    continuousStrictNegativeNullExpansion : Bool
    continuousStrictNegativeNullExpansionIsTrue : continuousStrictNegativeNullExpansion ≡ true
    compactnessPaysUniformNegativeExpansionMargin : Bool
    compactnessPaysUniformNegativeExpansionMarginIsTrue : compactnessPaysUniformNegativeExpansionMargin ≡ true
    uniformNegativeExpansionMarginMeaning : String
    uniformAffineFocusingBound : Bool
    uniformAffineFocusingBoundIsTrue : uniformAffineFocusingBound ≡ true
    uniformAffineFocusingBoundMeaning : String
    futureNullNormalDirectionFibreCompact : Bool
    futureNullNormalDirectionFibreCompactIsTrue : futureNullNormalDirectionFibreCompact ≡ true
    futureNullNormalDirectionFibreMeaning : String
    boundedGeneratorParameterDomainCompact : Bool
    boundedGeneratorParameterDomainCompactIsTrue : boundedGeneratorParameterDomainCompact ≡ true
    compactGeneratorDomainMeaning : String
    nullExponentialGeneratorMapContinuous : Bool
    nullExponentialGeneratorMapContinuousIsTrue : nullExponentialGeneratorMapContinuous ≡ true
    futureHorismosCoveredByBoundedGeneratorImage : Bool
    futureHorismosCoveredByBoundedGeneratorImageIsTrue : futureHorismosCoveredByBoundedGeneratorImage ≡ true
    futureHorismosClosedUnderGlobalHyperbolicity : Bool
    futureHorismosClosedUnderGlobalHyperbolicityIsTrue : futureHorismosClosedUnderGlobalHyperbolicity ≡ true
    compactParameterImagePaysHorismosCompactness : Bool
    compactParameterImagePaysHorismosCompactnessIsTrue : compactParameterImagePaysHorismosCompactness ≡ true
    compactnessOwnerInternallyReprovesContinuumTopology : Bool
    compactnessOwnerInternallyReprovesContinuumTopologyIsFalse : compactnessOwnerInternallyReprovesContinuumTopology ≡ false

open PenroseHorismosCompactnessBoundary public

canonicalPenroseHorismosCompactnessBoundary : PenroseHorismosCompactnessBoundary
canonicalPenroseHorismosCompactnessBoundary = record
  { compactTrappedSurfaceCarrier = true
  ; compactTrappedSurfaceCarrierIsTrue = refl
  ; continuousStrictNegativeNullExpansion = true
  ; continuousStrictNegativeNullExpansionIsTrue = refl
  ; compactnessPaysUniformNegativeExpansionMargin = true
  ; compactnessPaysUniformNegativeExpansionMarginIsTrue = refl
  ; uniformNegativeExpansionMarginMeaning =
      "on a compact trapped surface, continuous future null expansions that are strictly negative admit a uniform epsilon > 0 with theta <= -epsilon"
  ; uniformAffineFocusingBound = true
  ; uniformAffineFocusingBoundIsTrue = refl
  ; uniformAffineFocusingBoundMeaning =
      "the uniform negative expansion margin feeds the null focusing estimate to give one finite affine-length ceiling L valid for every relevant future null generator"
  ; futureNullNormalDirectionFibreCompact = true
  ; futureNullNormalDirectionFibreCompactIsTrue = refl
  ; futureNullNormalDirectionFibreMeaning =
      "the compact fibre is the normalized/projectivized future null-normal direction fibre; raw nonzero null normal vectors are scale-noncompact and are not the carrier used here"
  ; boundedGeneratorParameterDomainCompact = true
  ; boundedGeneratorParameterDomainCompactIsTrue = refl
  ; compactGeneratorDomainMeaning =
      "compact trapped surface T times its compact normalized future-null normal-direction fibre times a closed bounded affine interval [0,L] forms the compact generator parameter domain"
  ; nullExponentialGeneratorMapContinuous = true
  ; nullExponentialGeneratorMapContinuousIsTrue = refl
  ; futureHorismosCoveredByBoundedGeneratorImage = true
  ; futureHorismosCoveredByBoundedGeneratorImageIsTrue = refl
  ; futureHorismosClosedUnderGlobalHyperbolicity = true
  ; futureHorismosClosedUnderGlobalHyperbolicityIsTrue = refl
  ; compactParameterImagePaysHorismosCompactness = true
  ; compactParameterImagePaysHorismosCompactnessIsTrue = refl
  ; compactnessOwnerInternallyReprovesContinuumTopology = false
  ; compactnessOwnerInternallyReprovesContinuumTopologyIsFalse = refl
  }

record PenroseCompactnessInterpretationBoundary : Set where
  field
    pointwiseNegativeExpansionDoesNotAloneGiveUniformBound : Bool
    pointwiseNegativeExpansionDoesNotAloneGiveUniformBoundIsTrue : pointwiseNegativeExpansionDoesNotAloneGiveUniformBound ≡ true
    rawNullNormalVectorFibreIsNotCompactDirectionFibre : Bool
    rawNullNormalVectorFibreIsNotCompactDirectionFibreIsTrue : rawNullNormalVectorFibreIsNotCompactDirectionFibre ≡ true
    boundedAffineParameterDoesNotAloneMakeHorismosCompact : Bool
    boundedAffineParameterDoesNotAloneMakeHorismosCompactIsTrue : boundedAffineParameterDoesNotAloneMakeHorismosCompact ≡ true
    continuousImageCompactnessRequiresCompactDomain : Bool
    continuousImageCompactnessRequiresCompactDomainIsTrue : continuousImageCompactnessRequiresCompactDomain ≡ true
    compactGeneratorImageIsNotAutomaticallyHorismos : Bool
    compactGeneratorImageIsNotAutomaticallyHorismosIsTrue : compactGeneratorImageIsNotAutomaticallyHorismos ≡ true
    horismosClosednessIsSeparateCausalTopologicalPayment : Bool
    horismosClosednessIsSeparateCausalTopologicalPaymentIsTrue : horismosClosednessIsSeparateCausalTopologicalPayment ≡ true
    horismosCompactnessPaymentDoesNotProveGlobalIncompleteness : Bool
    horismosCompactnessPaymentDoesNotProveGlobalIncompletenessIsTrue : horismosCompactnessPaymentDoesNotProveGlobalIncompleteness ≡ true

open PenroseCompactnessInterpretationBoundary public

canonicalPenroseCompactnessInterpretationBoundary : PenroseCompactnessInterpretationBoundary
canonicalPenroseCompactnessInterpretationBoundary = record
  { pointwiseNegativeExpansionDoesNotAloneGiveUniformBound = true
  ; pointwiseNegativeExpansionDoesNotAloneGiveUniformBoundIsTrue = refl
  ; rawNullNormalVectorFibreIsNotCompactDirectionFibre = true
  ; rawNullNormalVectorFibreIsNotCompactDirectionFibreIsTrue = refl
  ; boundedAffineParameterDoesNotAloneMakeHorismosCompact = true
  ; boundedAffineParameterDoesNotAloneMakeHorismosCompactIsTrue = refl
  ; continuousImageCompactnessRequiresCompactDomain = true
  ; continuousImageCompactnessRequiresCompactDomainIsTrue = refl
  ; compactGeneratorImageIsNotAutomaticallyHorismos = true
  ; compactGeneratorImageIsNotAutomaticallyHorismosIsTrue = refl
  ; horismosClosednessIsSeparateCausalTopologicalPayment = true
  ; horismosClosednessIsSeparateCausalTopologicalPaymentIsTrue = refl
  ; horismosCompactnessPaymentDoesNotProveGlobalIncompleteness = true
  ; horismosCompactnessPaymentDoesNotProveGlobalIncompletenessIsTrue = refl
  }

causalBoundaryConsumer : Set
causalBoundaryConsumer = Causal.CausalFutureHorismosBoundary

focusingConsumer : Set
focusingConsumer = Focusing.NullOpticalFocusingBoundary

horismosCompactnessOwnerPromotesPenroseConclusion : Bool
horismosCompactnessOwnerPromotesPenroseConclusion = false

horismosCompactnessOwnerPromotesPenroseConclusionIsFalse :
  horismosCompactnessOwnerPromotesPenroseConclusion ≡ false
horismosCompactnessOwnerPromotesPenroseConclusionIsFalse = refl
