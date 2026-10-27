{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyGTPSProjectionProducerRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Quantum.QuantumMereologyGTPSProjectionProducerAuthorityExact as P

finite-hs-projector-source-written :
  P.FiniteHilbertSchmidtProjectorSourceWritten
    P.canonicalGTPSProjectionProducerStatus ≡ true
finite-hs-projector-source-written =
  P.FiniteHilbertSchmidtProjectorSourceWrittenIsTrue
    P.canonicalGTPSProjectionProducerStatus

finite-source-score-instantiated :
  P.FiniteSourceGTPSShortTimeScoreInstantiated
    P.canonicalGTPSProjectionProducerStatus ≡ true
finite-source-score-instantiated =
  P.FiniteSourceGTPSShortTimeScoreInstantiatedIsTrue
    P.canonicalGTPSProjectionProducerStatus

physical-source-gtps-remains-open :
  P.PhysicalSourceGTPSAutomaticallyIdentified
    P.canonicalGTPSProjectionProducerStatus ≡ false
physical-source-gtps-remains-open =
  P.PhysicalSourceGTPSAutomaticallyIdentifiedIsFalse
    P.canonicalGTPSProjectionProducerStatus
