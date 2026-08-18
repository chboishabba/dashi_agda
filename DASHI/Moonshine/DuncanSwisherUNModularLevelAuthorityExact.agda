module DASHI.Moonshine.DuncanSwisherUNModularLevelAuthorityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Equation (2.4) defines
--
--   f | U_N = (1/N) sum_{b mod N} f | V_N^{-1} T^b
--
-- and gives the exact Laurent q-expansion law
--
--   c_n(f | U_N) = c_{nN}(f).
--
-- Lemma 2.4 proves
--
--   f modular for Gamma_0(N^2)
--     =>
--   f | U_N modular for Gamma_0(N).
--
-- DASHI DISCIPLINE
--
-- The modular functions used by Duncan--Swisher have poles, so their q-series
-- must use the signed Laurent carrier Z -> Z.  This authority therefore pins
-- analytic U_N to FormalLaurentQSeriesUNExact, not to the Nat-indexed oldform
-- carrier used elsewhere in the repo.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
  renaming (_*_ to _*ℤ_)

import DASHI.Moonshine.FormalLaurentQSeriesUNExact as Laurent

postulate
  ModularFunction : Set
  qExpansion : ModularFunction → Laurent.FormalLaurentQSeries
  ModularForGamma0 : Nat → ModularFunction → Set
  analyticUN : Nat → ModularFunction → ModularFunction

  -- Same-object q-expansion law from equation (2.4).
  analyticUNCoefficientLaw :
    (N : Nat) → (f : ModularFunction) → (n : ℤ) →
    qExpansion (analyticUN N f) n
    ≡ Laurent.UN N (qExpansion f) n

  -- Duncan--Swisher Lemma 2.4.
  analyticUNLowersSquareLevel :
    (N : Nat) → (f : ModularFunction) →
    ModularForGamma0 (N * N) f →
    ModularForGamma0 N (analyticUN N f)

analyticUNCoefficientIsSelectedSource :
  (N : Nat) → (f : ModularFunction) → (n : ℤ) →
  qExpansion (analyticUN N f) n
  ≡ qExpansion f ((+ N) *ℤ n)
analyticUNCoefficientIsSelectedSource N f n =
  analyticUNCoefficientLaw N f n

record AnalyticUNLevelLoweringWitness
    (N : Nat) (f : ModularFunction) : Set where
  field
    sourceSquareLevel : ModularForGamma0 (N * N) f

open AnalyticUNLevelLoweringWitness public

loweredModularity :
  (N : Nat) → (f : ModularFunction) →
  AnalyticUNLevelLoweringWitness N f →
  ModularForGamma0 N (analyticUN N f)
loweredModularity N f witness =
  analyticUNLowersSquareLevel N f (sourceSquareLevel witness)

record DuncanSwisherUNModularLevelAuthorityBoundary : Set where
  field
    analyticUNDefinitionImported : Bool
    signedLaurentExpansionUsed : Bool
    coefficientSelectorSameObjectPinned : Bool
    lemma24LevelLoweringImported : Bool
    NatIndexedOldformCarrierUsedForMeromorphicHauptmodul : Bool
    etaHauptmodulObjectsConstructedHere : Bool
    DelignePadicRigidityConstructedHere : Bool

canonicalDuncanSwisherUNModularLevelAuthorityBoundary :
  DuncanSwisherUNModularLevelAuthorityBoundary
canonicalDuncanSwisherUNModularLevelAuthorityBoundary = record
  { analyticUNDefinitionImported = true
  ; signedLaurentExpansionUsed = true
  ; coefficientSelectorSameObjectPinned = true
  ; lemma24LevelLoweringImported = true
  ; NatIndexedOldformCarrierUsedForMeromorphicHauptmodul = false
  ; etaHauptmodulObjectsConstructedHere = false
  ; DelignePadicRigidityConstructedHere = false
  }
