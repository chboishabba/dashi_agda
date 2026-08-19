module DASHI.Physics.Closure.NSTriadKNViscousExchangeOddCancellationRound87Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Pierre Serre.
-- Title: "Linear Representations of Finite Groups".
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND87 / EXCHANGE-ODD CANCELLATION SURVIVES VISCOUS WEIGHTING
--
-- The Round87 viscous coefficient for one transfer triad and denominator mode
-- m is
--
--   c(p,q;k,m) = 2 nu [p dot q + |m|^2 - |k|^2].
--
-- It is invariant under p<->q.  Consequently any physical ordered-pair sector
-- that is genuinely exchange odd cancels before and after multiplication by
-- this coefficient.  The same is true of the centred signed-transfer residual
-- (c+M) tau used by the Round87 viscous aggregation theorem.
--
-- This means C2 exchange cancellation is not part of the new signed-residual
-- obstruction.  Only exchange-even/unpaired transfer survives.  The existing
-- Round73 physical HH/CC exchange-sector identification remains the source-side
-- theorem needed to exploit this on the literal Fourier carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadExchangeCharacterRound73Exact as Exchange

record CommonViscousWeightPair : Set where
  constructor common-viscous-weight-pair
  field
    pair : Exchange.ExchangePair
    commonCoefficient : ℚ

open CommonViscousWeightPair public

weightedPairSum : CommonViscousWeightPair → ℚ
weightedPairSum weighted =
  commonCoefficient weighted * Exchange.forward (pair weighted)
  + commonCoefficient weighted * Exchange.reversed (pair weighted)

centredWeightedPairSum : ℚ → CommonViscousWeightPair → ℚ
centredWeightedPairSum margin weighted =
  (commonCoefficient weighted + margin) * Exchange.forward (pair weighted)
  + (commonCoefficient weighted + margin) * Exchange.reversed (pair weighted)

exchangeOddWeightedPairCancels :
  ∀ {weighted} →
  Exchange.CertifiedExchangeOdd (pair weighted) →
  weightedPairSum weighted ≡ 0ℚ
exchangeOddWeightedPairCancels {weighted} odd
  rewrite Exchange.reversedIsNegative odd =
  solve
    ( commonCoefficient weighted
    ∷ Exchange.forward (pair weighted)
    ∷ [])

exchangeOddCentredResidualCancels :
  ∀ margin {weighted} →
  Exchange.CertifiedExchangeOdd (pair weighted) →
  centredWeightedPairSum margin weighted ≡ 0ℚ
exchangeOddCentredResidualCancels margin {weighted} odd
  rewrite Exchange.reversedIsNegative odd =
  solve
    ( margin ∷ commonCoefficient weighted
    ∷ Exchange.forward (pair weighted)
    ∷ [])

round87ExchangeOddCancellationSurvivesViscousGeometryWeight : Bool
round87ExchangeOddCancellationSurvivesViscousGeometryWeight = true

round87ExchangeOddCancellationSurvivesCentredResidual : Bool
round87ExchangeOddCancellationSurvivesCentredResidual = true

round87PhysicalHHCCExchangeSectorIdentificationConstructed : Bool
round87PhysicalHHCCExchangeSectorIdentificationConstructed =
  Exchange.round73PhysicalHHCCExchangeSectorIdentificationConstructed

round87ExchangeOddCancellationSurvivesViscousGeometryWeightIsTrue :
  round87ExchangeOddCancellationSurvivesViscousGeometryWeight ≡ true
round87ExchangeOddCancellationSurvivesViscousGeometryWeightIsTrue = refl
