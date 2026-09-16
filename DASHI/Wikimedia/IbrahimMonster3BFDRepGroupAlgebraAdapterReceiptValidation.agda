module DASHI.Wikimedia.IbrahimMonster3BFDRepGroupAlgebraAdapterReceiptValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BFDRepGroupAlgebraAdapterReceiptExact as P

sourceReceiptRegression :
  P.FDRepGroupAlgebraAdapterBoundary.leanAdapterSourceWritten
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ true
  × P.FDRepGroupAlgebraAdapterBoundary.sameActionEquationWritten
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ true
  × P.FDRepGroupAlgebraAdapterBoundary.wholeCharacterToIsotypicTheoremWritten
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ false
sourceReceiptRegression = refl , refl , refl

certificationRegression :
  P.FDRepGroupAlgebraAdapterBoundary.leanKernelReceiptObserved
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ false
  × P.FDRepGroupAlgebraAdapterBoundary.agdaTransportObserved
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ false
  × P.FDRepGroupAlgebraAdapterBoundary.oeisCreatesAdapterTheorem
    P.canonicalFDRepGroupAlgebraAdapterBoundary
  ≡ false
certificationRegression = refl , refl , refl
