module DASHI.Physics.Closure.NSTriadKNCriticalResidualQuadraticVariationRound156Exact where

------------------------------------------------------------------------
-- ROUND156 / FINITE QUADRATIC-VARIATION PAYMENT WITHOUT CARDINALITY TAX
--
-- Cross-pollination:
--   * RH G21: retain two independent residual channels rather than collapsing
--     them to one absolute-value envelope.
--   * YM Round40--42: remove exact cancellation fibres first, then estimate
--     only the surviving residual owner coordinates.
--
-- After R154--R155, the natural dynamic object is a finite list of signed
-- pairings
--
--      sum_i a_i b_i,
--
-- where a_i is the critical-dissipation-side residual and b_i is the
-- normalized-curl / trajectory residual companion.  The repository already
-- contains a genuine finite Gram proof of Cauchy--Schwarz.  This file promotes
-- that theorem to the exact A-facing vocabulary:
--
--   production^2 <= dissipationVariation * companionQuadraticVariation.
--
-- There is NO fibre cardinality, shell count, matching number or Wiener l1
-- factor.  The remaining PDE theorem is now sharply typed: construct this
-- residual pairing from the physical R144/R155 trajectory and prove a
-- cutoff-independent time-integrated budget on the companion quadratic
-- variation.  The latter is trajectory information, so it is not contradicted
-- by the static scaling no-go of Round151.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Product.Base using (_×_)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

ResidualPair : Set
ResidualPair = ℚ × ℚ

signedResidualProduction : List ResidualPair → ℚ
signedResidualProduction = L2.pairDot

criticalDissipationVariation : List ResidualPair → ℚ
criticalDissipationVariation = L2.leftNormSquared

companionQuadraticVariation : List ResidualPair → ℚ
companionQuadraticVariation = L2.rightNormSquared

residualProductionSquare : List ResidualPair → ℚ
residualProductionSquare pairs = L2.square (signedResidualProduction pairs)

finiteResidualQuadraticVariationPayment :
  (pairs : List ResidualPair) →
  residualProductionSquare pairs
  ≤ criticalDissipationVariation pairs * companionQuadraticVariation pairs
finiteResidualQuadraticVariationPayment = L2.finiteCauchySchwarzSquared

record PhysicalResidualPairingTarget : Set₁ where
  constructor physical-residual-pairing-target
  field
    Cutoff : Set
    residualPairs : Cutoff → List ResidualPair

    -- Same-object identification with the complete signed physical production
    -- accumulated after the R154 nuisance quotient and R155 trajectory
    -- telescope.  This remains the physical bridge, not a free theorem receipt.
    PhysicalSignedProduction : Cutoff → Set
    physicalSignedProduction : (N : Cutoff) → PhysicalSignedProduction N

    PairingIdentifiesPhysicalProduction : Set
    pairingIdentifiesPhysicalProduction : PairingIdentifiesPhysicalProduction

    -- The decisive new dynamic producer.  It must be uniform in cutoff and
    -- time-integrable; no value is assumed here.
    CutoffUniformCompanionQuadraticVariationBudget : Set
    cutoffUniformCompanionQuadraticVariationBudget :
      CutoffUniformCompanionQuadraticVariationBudget

open PhysicalResidualPairingTarget public

-- Once a physical target is constructed, the finite Cauchy--Schwarz part is
-- automatic at every cutoff.  This theorem intentionally does not pretend the
-- abstract Set-valued physical identification is already instantiated.
finitePaymentAvailableAtEveryCutoff :
  (T : PhysicalResidualPairingTarget) →
  (N : Cutoff T) →
  residualProductionSquare (residualPairs T N)
  ≤ criticalDissipationVariation (residualPairs T N)
      * companionQuadraticVariation (residualPairs T N)
finitePaymentAvailableAtEveryCutoff T N =
  finiteResidualQuadraticVariationPayment (residualPairs T N)

round156FiniteResidualQuadraticVariationPaymentClosed : Bool
round156FiniteResidualQuadraticVariationPaymentClosed = true

round156FibreCardinalityTaxIntroduced : Bool
round156FibreCardinalityTaxIntroduced = false

round156WienerL1FactorIntroduced : Bool
round156WienerL1FactorIntroduced = false

round156PhysicalCompanionQuadraticVariationBudgetClosed : Bool
round156PhysicalCompanionQuadraticVariationBudgetClosed = false

round156PackageAClosed : Bool
round156PackageAClosed = false

round156FiniteResidualQuadraticVariationPaymentClosedIsTrue :
  round156FiniteResidualQuadraticVariationPaymentClosed ≡ true
round156FiniteResidualQuadraticVariationPaymentClosedIsTrue = refl

round156PackageAClosedIsFalse : round156PackageAClosed ≡ false
round156PackageAClosedIsFalse = refl
