module DASHI.Physics.Closure.NSTriadKNLowLegFrameFactorizationRound73Exact where

------------------------------------------------------------------------
-- ROUND73 / LH-HL SOURCE-NATIVE FRAME TESTBED
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Round72 showed LH/HL raw multiplicity is controlled by the low shell but that
-- this remains summable.  The stronger Round73 test is to factor the SAME
-- StaticPhysicalShellPairing coefficient according to physical roles:
--
--     triadValue = lowLegAmplitude * highResponseCoefficient.
--
-- The field names fix the intended source section of the Round72 rescaling
-- fibre.  They are not arbitrary x/y optimization variables.  Once a physical
-- PDE theorem constructs these fields from Fourier velocity/projector data, the
-- factor list plugs directly into the Round72 Cauchy and Round73 frame bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as R72


data LowLegRole : Set where
  lowFromP lowFromQ : LowLegRole

record LowLegPhysicalFactorization
    (pairing : Shell.StaticPhysicalShellPairing) : Set where
  constructor low-leg-physical-factorization
  field
    classified : Support.ClassifiedPhysicalTriad
    role : LowLegRole
    roleMatchesClass :
      (role ≡ lowFromP → Support.sourceClass classified ≡ Support.LH) ×
      (role ≡ lowFromQ → Support.sourceClass classified ≡ Support.HL)
    lowLegAmplitude : ℚ
    highResponseCoefficient : ℚ
    sameTriadValueFactorization :
      Shell.triadValue pairing (Support.incidence classified)
      ≡ lowLegAmplitude * highResponseCoefficient

open LowLegPhysicalFactorization public

canonicalLowLegFactor :
  ∀ {pairing} → LowLegPhysicalFactorization pairing →
  R72.FactorizedContribution
canonicalLowLegFactor factor =
  R72.factorized-contribution
    (lowLegAmplitude factor)
    (highResponseCoefficient factor)

canonicalLowLegFactors :
  ∀ {pairing} → List (LowLegPhysicalFactorization pairing) →
  List R72.FactorizedContribution
canonicalLowLegFactors [] = []
canonicalLowLegFactors (factor ∷ rest) =
  canonicalLowLegFactor factor ∷ canonicalLowLegFactors rest

lowLegCharge :
  ∀ {pairing} → List (LowLegPhysicalFactorization pairing) → ℚ
lowLegCharge factors = R72.concentrationCharge (canonicalLowLegFactors factors)

lowLegEffectiveComplexity :
  ∀ {pairing} → List (LowLegPhysicalFactorization pairing) → ℚ
lowLegEffectiveComplexity factors =
  R72.effectiveComplexity (canonicalLowLegFactors factors)

round73LowLegPhysicalFactorizationCarrierConstructed : Bool
round73LowLegPhysicalFactorizationCarrierConstructed = true

round73LiteralLHHLVelocityFactorizationConstructed : Bool
round73LiteralLHHLVelocityFactorizationConstructed = false

round73LowLegPhysicalFactorizationCarrierConstructedIsTrue :
  round73LowLegPhysicalFactorizationCarrierConstructed ≡ true
round73LowLegPhysicalFactorizationCarrierConstructedIsTrue = refl

round73LiteralLHHLVelocityFactorizationConstructedIsFalse :
  round73LiteralLHHLVelocityFactorizationConstructed ≡ false
round73LiteralLHHLVelocityFactorizationConstructedIsFalse = refl
