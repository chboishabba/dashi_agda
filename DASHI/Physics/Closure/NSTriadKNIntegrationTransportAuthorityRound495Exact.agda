module DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact where

------------------------------------------------------------------------
-- ROUND495 / INTEGRATION TRANSPORT AUTHORITY FOR THE STRICT R423 WELD
--
-- The physical dynamics intentionally abstracts temporal integration as
--
--   integrateTo : (Time -> Q) -> Time -> Q.
--
-- That bare function type supplies no theorem saying integration respects
-- pointwise equality or finite addition.  R494 closes the instantaneous
-- normalization 2*C_k = literal companion_k, but lifting fixed-output sums to
-- the integrated strict R423 carrier therefore needs explicit integration laws.
--
-- These laws are standard analysis / carrier authority.  This interface does
-- not inhabit them and does not pay any Navier--Stokes estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

record IntegrationTransportAuthority
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ) : Set₁ where
  field
    integrateCongruent :
      (f g : Time → ℚ) →
      ((t : Time) → f t ≡ g t) →
      (terminal : Time) →
      integrateTo f terminal ≡ integrateTo g terminal

    integrateZero :
      (terminal : Time) →
      integrateTo (λ _ → 0ℚ) terminal ≡ 0ℚ

    integrateAdd :
      (f g : Time → ℚ) →
      (terminal : Time) →
      integrateTo (λ t → f t + g t) terminal
      ≡ integrateTo f terminal + integrateTo g terminal

open IntegrationTransportAuthority public

round495BareIntegrateToTypeSuppliesTransportLaws : Bool
round495BareIntegrateToTypeSuppliesTransportLaws = false

round495IntegrationTransportAuthorityIsStandardLayer : Bool
round495IntegrationTransportAuthorityIsStandardLayer = true

round495AuthorityInterfaceCreatesInhabitant : Bool
round495AuthorityInterfaceCreatesInhabitant = false

round495InstantaneousR494NormalizationAlreadyClosed : Bool
round495InstantaneousR494NormalizationAlreadyClosed = true

round495TrajectoryIntegratedCompanionWeldClosed : Bool
round495TrajectoryIntegratedCompanionWeldClosed = false

round495SignedSpacetimeEstimateClosed : Bool
round495SignedSpacetimeEstimateClosed = false

round495ClayPromotion : Bool
round495ClayPromotion = false

round495BareIntegrateToTypeSuppliesTransportLawsIsFalse :
  round495BareIntegrateToTypeSuppliesTransportLaws ≡ false
round495BareIntegrateToTypeSuppliesTransportLawsIsFalse = refl

round495AuthorityInterfaceCreatesInhabitantIsFalse :
  round495AuthorityInterfaceCreatesInhabitant ≡ false
round495AuthorityInterfaceCreatesInhabitantIsFalse = refl

round495ClayPromotionIsFalse : round495ClayPromotion ≡ false
round495ClayPromotionIsFalse = refl
