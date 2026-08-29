{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact where

------------------------------------------------------------------------
-- ROUND114 BC1: FINITE CMP116 DEMANDS -> ONE ACTUAL COMMON RADIUS OBJECT
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Round104 already proves that the four finite normalized analytic demands from
-- CMP116 Sect.1 admit the canonical positive radius
--
--       epsilon_* = 1 / (2 (S + 1)),
--
-- and that each individual demand times epsilon_* is < 1.  Round103's BC1
-- consumer, however, still exposes an abstract `CMP116CommonAnalyticRadius`.
-- This file closes that algebraic mismatch: from the finite demand data we build
-- one literal common-radius object whose four coordinate-domain predicates are
-- exactly the four source smallness inequalities.
--
-- Thus existence/positivity of a common radius is not a remaining physical
-- theorem.  The physical source seam is only extraction of the finite normalized
-- demand constants from the literal CMP116 family and identification of the
-- actual U/J/local-activity/substituted-background coordinates with these four
-- inequalities on the same scale/volume/background.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon

canonicalCMP116CommonDomain :
  ∀ {Scale Volume : Set} →
  Canon.CMP116FiniteNormalizedAnalyticDemands →
  Common.CMP116CommonAnalyticRadius Scale Volume
canonicalCMP116CommonDomain d = record
  { Common.CMP116CommonAnalyticRadius.radius = Canon.canonicalCommonRadius d
  ; Common.CMP116CommonAnalyticRadius.radiusPositive =
      Canon.canonicalCommonRadiusPositive d
  ; Common.CMP116CommonAnalyticRadius.BackgroundCoordinateInside =
      λ _ _ →
        Canon.propagatorDemand d * Canon.canonicalCommonRadius d < 1ℚ
  ; Common.CMP116CommonAnalyticRadius.SourceCoordinateInside =
      λ _ _ →
        Canon.linearizingFixedPointDemand d * Canon.canonicalCommonRadius d < 1ℚ
  ; Common.CMP116CommonAnalyticRadius.LocalActivityCoordinateInside =
      λ _ _ →
        Canon.minimizerFixedPointDemand d * Canon.canonicalCommonRadius d < 1ℚ
  ; Common.CMP116CommonAnalyticRadius.SubstitutedBackgroundInside =
      λ _ _ →
        Canon.substitutedBackgroundDemand d * Canon.canonicalCommonRadius d < 1ℚ
  ; Common.CMP116CommonAnalyticRadius.backgroundCoordinateInside =
      λ _ _ → Canon.propagatorDemandPaid d
  ; Common.CMP116CommonAnalyticRadius.sourceCoordinateInside =
      λ _ _ → Canon.linearizingFixedPointDemandPaid d
  ; Common.CMP116CommonAnalyticRadius.localActivityCoordinateInside =
      λ _ _ → Canon.minimizerFixedPointDemandPaid d
  ; Common.CMP116CommonAnalyticRadius.substitutedBackgroundInside =
      λ _ _ → Canon.substitutedBackgroundDemandPaid d
  }

canonicalFirstSecondDerivativeSameRadius :
  ∀ {Scale Volume : Set}
    (d : Canon.CMP116FiniteNormalizedAnalyticDemands) →
  Common.FirstSecondDerivativeUseSameRadius
    (canonicalCMP116CommonDomain {Scale} {Volume} d)
canonicalFirstSecondDerivativeSameRadius d = record
  { Common.FirstSecondDerivativeUseSameRadius.FirstDerivativeCauchyValid =
      λ _ _ → Canon.totalDemand d * Canon.canonicalCommonRadius d < 1ℚ
  ; Common.FirstSecondDerivativeUseSameRadius.SecondDerivativeCauchyValid =
      λ _ _ → Canon.totalDemand d * Canon.canonicalCommonRadius d < 1ℚ
  ; Common.FirstSecondDerivativeUseSameRadius.firstDerivativeCauchyValid =
      λ _ _ → Canon.totalDemandTimesRadiusBelowOne d
  ; Common.FirstSecondDerivativeUseSameRadius.secondDerivativeCauchyValid =
      λ _ _ → Canon.totalDemandTimesRadiusBelowOne d
  }

cmp116FiniteDemandsToCommonRadiusObjectLevel : ProofLevel
cmp116FiniteDemandsToCommonRadiusObjectLevel = machineChecked

cmp116FirstSecondDerivativeShareCanonicalRadiusLevel : ProofLevel
cmp116FirstSecondDerivativeShareCanonicalRadiusLevel = machineChecked

-- Remaining physical BC1 radius seam: extract the four finite normalized
-- demands from CMP116 (1.13)--(1.22) on the literal generated family and prove
-- that the physical source/background/local-activity coordinates are exactly the
-- four predicates used above.  No separate epsilon-existence theorem remains.
literalCMP116FiniteDemandExtractionAndCoordinateIdentificationLevel : ProofLevel
literalCMP116FiniteDemandExtractionAndCoordinateIdentificationLevel = conditional
