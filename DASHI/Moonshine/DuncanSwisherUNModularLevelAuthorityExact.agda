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
-- and gives the exact q-expansion law
--
--   c_n(f | U_N) = c_{nN}(f).
--
-- Lemma 2.4 proves the genuine analytic level-lowering theorem
--
--   f modular for Gamma_0(N^2)
--     =>
--   f | U_N modular for Gamma_0(N).
--
-- DASHI DISCIPLINE
--
-- FormalQSeriesUNLevelLoweringExact already constructs the coefficient selector
-- UN N on Nat -> Z.  This authority surface forces the analytic source operator
-- to have THAT SAME q-expansion pointwise.  Thus analytic modularity and formal
-- coefficient arithmetic cannot silently become two unrelated operators with
-- the same name.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact as Q
import DASHI.Moonshine.FormalQSeriesUNLevelLoweringExact as U

------------------------------------------------------------------------
-- Source-facing analytic modular-function carriers.
------------------------------------------------------------------------

postulate
  ModularFunction : Set
  qExpansion : ModularFunction → Q.FormalQSeries
  ModularForGamma0 : Nat → ModularFunction → Set
  analyticUN : Nat → ModularFunction → ModularFunction

  -- Same-object q-expansion law from equation (2.4).
  analyticUNCoefficientLaw :
    (N : Nat) → (f : ModularFunction) → (n : Nat) →
    qExpansion (analyticUN N f) n ≡ U.UN N (qExpansion f) n

  -- Duncan--Swisher Lemma 2.4.
  analyticUNLowersSquareLevel :
    (N : Nat) → (f : ModularFunction) →
    ModularForGamma0 (N * N) f →
    ModularForGamma0 N (analyticUN N f)

------------------------------------------------------------------------
-- Local consequences use the formal operator, not another coefficient rule.
------------------------------------------------------------------------

analyticUNCoefficientIsSelectedSource :
  (N : Nat) → (f : ModularFunction) → (n : Nat) →
  qExpansion (analyticUN N f) n
  ≡ qExpansion f (N * n)
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

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DuncanSwisherUNModularLevelAuthorityBoundary : Set where
  field
    analyticUNDefinitionImported : Bool
    coefficientSelectorSameObjectPinned : Bool
    lemma24LevelLoweringImported : Bool
    formalCoefficientLawsReprovedAnalytically : Bool
    etaHauptmodulObjectsConstructedHere : Bool
    DelignePadicRigidityConstructedHere : Bool

canonicalDuncanSwisherUNModularLevelAuthorityBoundary :
  DuncanSwisherUNModularLevelAuthorityBoundary
canonicalDuncanSwisherUNModularLevelAuthorityBoundary = record
  { analyticUNDefinitionImported = true
  ; coefficientSelectorSameObjectPinned = true
  ; lemma24LevelLoweringImported = true
  ; formalCoefficientLawsReprovedAnalytically = false
  ; etaHauptmodulObjectsConstructedHere = false
  ; DelignePadicRigidityConstructedHere = false
  }
