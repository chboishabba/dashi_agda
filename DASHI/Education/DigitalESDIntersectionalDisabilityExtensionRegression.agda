module DASHI.Education.DigitalESDIntersectionalDisabilityExtensionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDIntersectionalDisabilityExtensionExact as X
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

bonnetteDOIRegression :
  Attr.AttributedSource.doiState X.bonnetteIntersectionalitySource
  ≡ Attr.doiRecorded "10.1080/1034912X.2025.2571758"
bonnetteDOIRegression = refl

bonnetteAnalysisNRegression : X.bonnetteAnalysisN ≡ 54
bonnetteAnalysisNRegression = refl

bonnetteCeilingRegression :
  X.bonnetteStrongestPaidImplication ≡ Cone.derivesBoundedContrast
bonnetteCeilingRegression = refl

waterfieldDOIRegression :
  Attr.AttributedSource.doiState X.waterfieldDisabilityComparatorSource
  ≡ Attr.doiRecorded "10.1177/01626434261454347"
waterfieldDOIRegression = refl

waterfieldDisabledNRegression : X.waterfieldDisabledRespondentN ≡ 48
waterfieldDisabledNRegression = refl
