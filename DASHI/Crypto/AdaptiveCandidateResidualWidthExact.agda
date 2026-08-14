module DASHI.Crypto.AdaptiveCandidateResidualWidthExact where

------------------------------------------------------------------------
-- FIBRE-LOCAL RESIDUAL WIDTH
--
-- Candidate fibres need not have uniform width.  The coarse observation may
-- leave one state, two states, or more.  A residual representation therefore
-- belongs over the observed fibre rather than being globally fixed-width.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

record ResidualWidthCertificate : Set where
  constructor residualWidthCertificate
  field
    fibreCardinality : Nat
    residualBits : Nat
    fits : fibreCardinality ≤ pow2 residualBits

open ResidualWidthCertificate public

uniqueNeedsZeroBits : ResidualWidthCertificate
uniqueNeedsZeroBits = residualWidthCertificate 1 0 (s≤s z≤n)

twoCandidatesFitOneBit : ResidualWidthCertificate
twoCandidatesFitOneBit = residualWidthCertificate 2 1 (s≤s (s≤s z≤n))

fourCandidatesFitTwoBits : ResidualWidthCertificate
fourCandidatesFitTwoBits =
  residualWidthCertificate 4 2
    (s≤s (s≤s (s≤s (s≤s z≤n))))

------------------------------------------------------------------------
-- Observation-dependent bundle.
------------------------------------------------------------------------

data ObservationClass : Set where
  ambiguousTwo identifiedOne : ObservationClass

residualCertificate : ObservationClass → ResidualWidthCertificate
residualCertificate ambiguousTwo = twoCandidatesFitOneBit
residualCertificate identifiedOne = uniqueNeedsZeroBits

widthBeforeObservation : residualBits (residualCertificate ambiguousTwo) ≡ 1
widthBeforeObservation = refl

widthAfterObservation : residualBits (residualCertificate identifiedOne) ≡ 0
widthAfterObservation = refl

observationShrinksResidualWidth :
  residualBits (residualCertificate identifiedOne) ≡ 0
  × residualBits (residualCertificate ambiguousTwo) ≡ 1
observationShrinksResidualWidth = refl , refl

------------------------------------------------------------------------
-- Worst-case and path-local storage are therefore different notions.  The
-- theorem surface intentionally stops before probability-weighted expected rate.
------------------------------------------------------------------------

record FibreLocalResidualBundle : Set₁ where
  constructor fibreLocalResidualBundle
  field
    Coarse : Set
    width : Coarse → Nat

open FibreLocalResidualBundle public

labBundle : FibreLocalResidualBundle
labBundle = fibreLocalResidualBundle ObservationClass
  (λ { ambiguousTwo → 1 ; identifiedOne → 0 })
