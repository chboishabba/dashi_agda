module DASHI.Wikimedia.IbrahimMonster3BFDRepSubmoduleAdapterReceiptValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BFDRepGroupAlgebraAdapterReceiptExact as P

submoduleAdapterRegression :
  P.FDRepGroupAlgebraAdapterBoundary.submoduleStabilityAdapterSourceWritten
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ true
  × P.FDRepGroupAlgebraAdapterBoundary.moduleSimpleTypeCanNowReenterRepresentationSide
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ true
  × P.FDRepGroupAlgebraAdapterBoundary.wholeCharacterToIsotypicTheoremWritten
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ false
submoduleAdapterRegression = refl , refl , refl

certificationRegression :
  P.FDRepGroupAlgebraAdapterBoundary.leanKernelReceiptObserved
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ false
  × P.FDRepGroupAlgebraAdapterBoundary.agdaTransportObserved
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ false
certificationRegression = refl , refl
