module DASHI.ComputerScience.RSA260BidiMksolActionChunkedStressValidationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.RSA260BidiMksolActionChunkedStressExact as P

chunkPlanRegression :
  P.MksolActionChunkedStressBoundary.chunkedExecutionPlanDefined
    P.canonicalMksolActionChunkedStressBoundary
  ≡ true
  × P.MksolActionChunkedStressBoundary.targetWorldCountIsThirtyFour
    P.canonicalMksolActionChunkedStressBoundary
  ≡ true
  × P.MksolActionChunkedStressBoundary.degreeR2R10HypothesisRetained
    P.canonicalMksolActionChunkedStressBoundary
  ≡ true
  × P.MksolActionChunkedStressBoundary.partialPrefixIsNotPortfolioReceipt
    P.canonicalMksolActionChunkedStressBoundary
  ≡ true
chunkPlanRegression = refl , refl , refl , refl

paymentRegression :
  P.MksolActionChunkedStressBoundary.completeThirtyFourWorldActionReceiptPaid
    P.canonicalMksolActionChunkedStressBoundary
  ≡ false
  × P.MksolActionChunkedStressBoundary.degreeR2R10BroaderAdequacyPaid
    P.canonicalMksolActionChunkedStressBoundary
  ≡ false
  × P.MksolActionChunkedStressBoundary.exactCADOMksolSameObjectContextPaid
    P.canonicalMksolActionChunkedStressBoundary
  ≡ false
paymentRegression = refl , refl , refl
