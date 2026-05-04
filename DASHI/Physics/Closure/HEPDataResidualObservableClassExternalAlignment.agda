module DASHI.Physics.Closure.HEPDataResidualObservableClassExternalAlignment where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataResidualObservableClassProtoReceipt as Proto
import DASHI.Physics.Closure.HEPDataResidualObservableClassRequest as Class
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack

------------------------------------------------------------------------
-- HEPData residual observable-class external alignment.
--
-- This module translates the internal phistar_50_76 fluctuationProfile
-- candidate into externally legible statistical/physics language.  It aligns
-- the class with an adjacent-bin finite-difference residual / local
-- bin-to-bin variation.  It is still not an accepted provider receipt and
-- still does not claim a calibrated significance, covariance-complete
-- comparison, or W3/W4/W5/W8 promotion.

data HEPDataResidualObservableClassExternalAlignmentStatus : Set where
  externallyLegibleClassAlignedButReceiptUnaccepted :
    HEPDataResidualObservableClassExternalAlignmentStatus

data HEPDataExternallyLegibleResidualClass : Set where
  adjacentBinFiniteDifferenceResidual :
    HEPDataExternallyLegibleResidualClass
  localBinToBinVariation :
    HEPDataExternallyLegibleResidualClass
  firstOrderDiscreteDerivativeProxy :
    HEPDataExternallyLegibleResidualClass
  covarianceNormalizedPullCandidate :
    HEPDataExternallyLegibleResidualClass

canonicalExternallyLegibleResidualClasses :
  List HEPDataExternallyLegibleResidualClass
canonicalExternallyLegibleResidualClasses =
  adjacentBinFiniteDifferenceResidual
  ∷ localBinToBinVariation
  ∷ firstOrderDiscreteDerivativeProxy
  ∷ covarianceNormalizedPullCandidate
  ∷ []

data HEPDataResidualObservableClassExternalAlignmentField : Set where
  alignmentInternalClass :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentExternalClass :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentPublishedObservable :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentFiniteDifferenceDefinition :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentBinPair :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentNonZeroDelta :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentDiscreteDerivativeProxy :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentUncertaintyBoundary :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentMinimalPublishableClaim :
    HEPDataResidualObservableClassExternalAlignmentField
  alignmentAuthorityBoundary :
    HEPDataResidualObservableClassExternalAlignmentField

canonicalExternalAlignmentFields :
  List HEPDataResidualObservableClassExternalAlignmentField
canonicalExternalAlignmentFields =
  alignmentInternalClass
  ∷ alignmentExternalClass
  ∷ alignmentPublishedObservable
  ∷ alignmentFiniteDifferenceDefinition
  ∷ alignmentBinPair
  ∷ alignmentNonZeroDelta
  ∷ alignmentDiscreteDerivativeProxy
  ∷ alignmentUncertaintyBoundary
  ∷ alignmentMinimalPublishableClaim
  ∷ alignmentAuthorityBoundary
  ∷ []

record HEPDataResidualObservableClassExternalAlignment : Setω where
  field
    status :
      HEPDataResidualObservableClassExternalAlignmentStatus

    protoReceipt :
      Proto.HEPDataResidualObservableClassProtoReceipt

    internalClassSurface :
      Class.HEPDataResidualObservableClassRequestSurface

    internalKindIsFluctuationProfile :
      Class.HEPDataResidualObservableClassRequestSurface.residualObservableKind
        internalClassSurface
      ≡
      Class.fluctuationProfile

    externalPrimaryClass :
      HEPDataExternallyLegibleResidualClass

    externalPrimaryClassIsFiniteDifferenceResidual :
      externalPrimaryClass
      ≡
      adjacentBinFiniteDifferenceResidual

    acceptedExternalClassVocabulary :
      List HEPDataExternallyLegibleResidualClass

    acceptedExternalClassVocabularyIsCanonical :
      acceptedExternalClassVocabulary
      ≡
      canonicalExternallyLegibleResidualClasses

    alignmentFields :
      List HEPDataResidualObservableClassExternalAlignmentField

    alignmentFieldsAreCanonical :
      alignmentFields
      ≡
      canonicalExternalAlignmentFields

    externallyLegibleClassName :
      String

    publishedObservableName :
      String

    finiteDifferenceDefinition :
      String

    binPairDefinition :
      String

    nonZeroDeltaStatement :
      String

    discreteDerivativeProxyStatement :
      String

    uncertaintyBoundary :
      String

    minimalPublishableClaim :
      String

    providerFirstMissingReceipt :
      Pack.HEPDataResidualProviderFirstMissingReceipt

    providerFirstMissingReceiptIsResidualObservableClass :
      providerFirstMissingReceipt
      ≡
      Pack.firstMissingResidualObservableClass

    nonPromotionBoundary :
      List String

canonicalHEPDataResidualObservableClassExternalAlignment :
  HEPDataResidualObservableClassExternalAlignment
canonicalHEPDataResidualObservableClassExternalAlignment =
  record
    { status =
        externallyLegibleClassAlignedButReceiptUnaccepted
    ; protoReceipt =
        Proto.canonicalHEPDataResidualObservableClassProtoReceipt
    ; internalClassSurface =
        Proto.HEPDataResidualObservableClassProtoReceipt.proposedClassSurface
          Proto.canonicalHEPDataResidualObservableClassProtoReceipt
    ; internalKindIsFluctuationProfile =
        refl
    ; externalPrimaryClass =
        adjacentBinFiniteDifferenceResidual
    ; externalPrimaryClassIsFiniteDifferenceResidual =
        refl
    ; acceptedExternalClassVocabulary =
        canonicalExternallyLegibleResidualClasses
    ; acceptedExternalClassVocabularyIsCanonical =
        refl
    ; alignmentFields =
        canonicalExternalAlignmentFields
    ; alignmentFieldsAreCanonical =
        refl
    ; externallyLegibleClassName =
        "adjacent-bin finite-difference residual / local bin-to-bin variation"
    ; publishedObservableName =
        "CMS Drell-Yan 13 TeV differential cross section binned in phi*, mass window 50 <= M_ll < 76 GeV"
    ; finiteDifferenceDefinition =
        "r_i = y_i - y_(i+1) for adjacent bins; raw upstream t19 has r_0 = 228.59 - 225.69, while the normalized local artifact has r_0 = 188.4 - 185.09"
    ; binPairDefinition =
        "bin centers x_0 = 0.002 and x_1 = 0.006 from HEPData publication record ins2079374, table DOI 10.17182/hepdata.115656.v1/t19"
    ; nonZeroDeltaStatement =
        "raw upstream r_0 = 2.90 and normalized artifact r_0 = 3.3100000000000023; both are non-zero, but adapter semantics are not promoted here"
    ; discreteDerivativeProxyStatement =
        "first-order discrete derivative proxy over bin centers is available for raw or normalized surfaces; the selected surface is not promoted here"
    ; uncertaintyBoundary =
        "candidate diagonal-covariance normalized pull is 0.6169534835701825; this module does not claim statistical significance or full covariance adequacy"
    ; minimalPublishableClaim =
        "A non-collapsing adjacent-bin finite-difference residual exists for phistar_50_76 between bins 0 and 1; the remaining publishable step is an adapter-bound value-surface selection plus accepted authority route"
    ; providerFirstMissingReceipt =
        Pack.firstMissingResidualObservableClass
    ; providerFirstMissingReceiptIsResidualObservableClass =
        refl
    ; nonPromotionBoundary =
        "This module aligns DASHI fluctuationProfile with standard adjacent-bin finite-difference residual language"
        ∷ "It does not construct an accepted residualObservableClassReceipt"
        ∷ "It does not construct covariance-complete calibration or significance"
        ∷ "It does not choose between raw upstream t19 values and normalized local artifact values"
        ∷ "It does not construct theorem-side projection, defect projection, residual comparison law, accepted authority route, W3, W4, W5, or W8 promotion"
        ∷ []
    }
