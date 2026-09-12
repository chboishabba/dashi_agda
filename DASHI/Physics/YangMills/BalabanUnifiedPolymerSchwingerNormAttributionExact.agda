{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormAttributionExact where

------------------------------------------------------------------------
-- ATTRIBUTION OWNER FOR THE OPTIONAL UNIFIED POLYMER/SCHWINGER-NORM TACTIC
--
-- This source record survives theorem-interface minimization.  The cited works
-- motivate polymer activities, RG norms, decay weights, composite-operator
-- transport and gauge-theory RG organization.  Citation does NOT prove the
-- nonperturbative four-dimensional pure Yang--Mills quantitative clustering
-- theorem used by the Clay mass-gap consumer.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- David C. Brydges, P. K. Mitter and B. Scoppola,
-- "Critical (Phi^4)_{3,epsilon}", Communications in Mathematical Physics
-- 240 (2003), 281--327. DOI: 10.1007/s00220-003-0895-4.
--
-- P. K. Mitter,
-- "The Exact Renormalization Group", Encyclopedia of Mathematical Physics
-- (2006). DOI: 10.1016/B0-12-512666-2/00071-7.
--
-- Janos Polonyi and Kornel Sailer,
-- "Renormalization of Composite Operators", Physical Review D 63 (2001),
-- 105006. DOI: 10.1103/PhysRevD.63.105006.
--
-- Tadeusz Balaban, John Imbrie and Arthur Jaffe,
-- "Exact Renormalization Group for Gauge Theories", in Progress in Gauge
-- Field Theory (1984), pp. 79--103.
-- DOI: 10.1007/978-1-4757-0280-4_4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record UnifiedNormAttribution : Set where
  constructor unified-norm-attribution
  field
    brydgesDimockHurdDOI : String
    brydgesMitterScoppolaDOI : String
    mitterExactRGDOI : String
    polonyiSailerDOI : String
    balabanImbrieJaffeDOI : String

    sourcesMotivateProducerArchitecture : Bool
    sourcesMotivateProducerArchitectureIsTrue :
      sourcesMotivateProducerArchitecture ≡ true

    citationsProveFourDimensionalYMClustering : Bool
    citationsProveFourDimensionalYMClusteringIsFalse :
      citationsProveFourDimensionalYMClustering ≡ false

open UnifiedNormAttribution public

canonicalUnifiedNormAttribution : UnifiedNormAttribution
canonicalUnifiedNormAttribution =
  unified-norm-attribution
    "10.4153/CJM-1998-041-5"
    "10.1007/s00220-003-0895-4"
    "10.1016/B0-12-512666-2/00071-7"
    "10.1103/PhysRevD.63.105006"
    "10.1007/978-1-4757-0280-4_4"
    true refl
    false refl
