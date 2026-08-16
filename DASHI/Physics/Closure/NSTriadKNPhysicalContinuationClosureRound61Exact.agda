module DASHI.Physics.Closure.NSTriadKNPhysicalContinuationClosureRound61Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- ROUND 61 CONTRIBUTION
--
-- Close the final H same-object audit on the already-existing official Luo
-- continuation carrier.  This does NOT create a second continuation theorem.
-- It exposes the exact facts that the final owner/block argument must use:
--
--   * the Leray--Hopf solution underneath every official energy-time object is
--     literally the selected repository solution;
--   * the smooth cutoff integral bounded by the multiplier lane is exactly the
--     localized-gradient integral appearing in Luo's continuation criterion;
--   * the three-torus/unit-viscosity normalization is the source normalization;
--   * the continuation conclusion is obtained from smooth initial data,
--     solving the same periodic NS problem, and the localized limsup bound.
--
-- No Galerkin-limit premise appears here because the official continuation lane
-- is already formulated directly on the regular-before-terminal Leray--Hopf
-- solution.  If A1/F1 are constructed through Galerkin approximants, THEIR
-- producer must prove the nonlinear/localized limit passage before it can be
-- identified with this same solution; H does not accept a second approximation
-- carrier and does not hide such convergence in a Boolean receipt.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationClosureExact as Closure
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Source
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMultiplierKernelBoundExact as Multiplier

selectedLerayHopfSolutionIsSelectedSolution :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : Closure.OfficialLuoContinuationClosure InitialDatum Solution Time) →
  Source.LH.solution
    (Source.lerayHopfSolutionAt
      (Closure.sourceCarrier C)
      (Closure.initial C)
      (Closure.solution C))
  ≡ Closure.solution C
selectedLerayHopfSolutionIsSelectedSolution C =
  Source.lerayHopfSolutionMeaning
    (Closure.sourceCarrier C)
    (Closure.initial C)
    (Closure.solution C)

selectedLerayHopfInitialDatumIsSelectedInitialDatum :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : Closure.OfficialLuoContinuationClosure InitialDatum Solution Time) →
  Source.LH.initialDatum
    (Source.lerayHopfSolutionAt
      (Closure.sourceCarrier C)
      (Closure.initial C)
      (Closure.solution C))
  ≡ Closure.initial C
selectedLerayHopfInitialDatumIsSelectedInitialDatum C =
  Source.lerayHopfInitialMeaning
    (Closure.sourceCarrier C)
    (Closure.initial C)
    (Closure.solution C)

physicalSmoothCutoffBoundIsSourceContinuationBound :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : Closure.OfficialLuoContinuationClosure InitialDatum Solution Time) →
  (shell : Nat) →
  Source.localizedGradientIntegral
    (Closure.sourceCarrier C)
    (Closure.solution C)
    (Closure.terminal C)
    shell
  ≤ Source.universalDeltaBKM (Closure.sourceCarrier C)
physicalSmoothCutoffBoundIsSourceContinuationBound =
  Closure.officialSourceCutoffBound

physicalLocalizedLimsupIsLuoContinuationLimsup :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : Closure.OfficialLuoContinuationClosure InitialDatum Solution Time) →
  Source.LuoLocalizedGradientLimsupBound
    (Closure.sourceCarrier C)
    (Closure.solution C)
    (Closure.terminal C)
physicalLocalizedLimsupIsLuoContinuationLimsup =
  Closure.officialSourceLimsupBound

physicalDomainAndViscosityMatchLuo :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : Closure.OfficialLuoContinuationClosure InitialDatum Solution Time) →
  Source.SourceNormalizationMatchesLuo (Closure.sourceCarrier C)
physicalDomainAndViscosityMatchLuo C =
  Source.selectedSourceNormalization (Closure.sourceCarrier C)

physicalSelectedSolutionContinuesBeyondTerminal :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : Closure.OfficialLuoContinuationClosure InitialDatum Solution Time) →
  Source.ContinuesBeyond
    (Closure.sourceCarrier C)
    (Closure.initial C)
    (Closure.terminal C)
physicalSelectedSolutionContinuesBeyondTerminal =
  Closure.officialLuoContinuation

-- The final implication above consumes no `ContinuesBeyond` witness.  Its
-- ingredients are all fields already carried by C: smooth initial data and
-- the NS solution selection, plus the localized bound derived by the multiplier
-- lane.  This theorem exposes the exact proof term again so the non-circular
-- dependency is visible at the Round61 cut rather than represented by a flag.
physicalContinuationFromLocalizedCutoffBounds :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : Closure.OfficialLuoContinuationClosure InitialDatum Solution Time) →
  ((shell : Nat) →
    Source.localizedGradientIntegral
      (Closure.sourceCarrier C)
      (Closure.solution C)
      (Closure.terminal C)
      shell
    ≤ Source.universalDeltaBKM (Closure.sourceCarrier C)) →
  Source.ContinuesBeyond
    (Closure.sourceCarrier C)
    (Closure.initial C)
    (Closure.terminal C)
physicalContinuationFromLocalizedCutoffBounds C cutoffBound =
  let
    carrier = Closure.sourceCarrier C
    selection = Closure.sourceSelection C
    limsup =
      Source.pointwiseThresholdImpliesLimsupBound
        carrier
        (Closure.solution C)
        (Closure.terminal C)
        cutoffBound
  in
  Source.regularityGivesContinuationImported
    carrier
    (Closure.initial C)
    (Closure.solution C)
    (Closure.terminal C)
    (Source.solvesFromInitialData selection)
    (Source.luoTheorem11RegularityImported
      carrier
      (Closure.initial C)
      (Closure.solution C)
      (Closure.terminal C)
      (Source.smoothInitialData selection)
      (Source.solvesFromInitialData selection)
      limsup)

physicalContinuationSameObjectAuditClosed : Bool
physicalContinuationSameObjectAuditClosed = true

physicalContinuationSameObjectAuditClosedIsTrue :
  physicalContinuationSameObjectAuditClosed ≡ true
physicalContinuationSameObjectAuditClosedIsTrue = refl
