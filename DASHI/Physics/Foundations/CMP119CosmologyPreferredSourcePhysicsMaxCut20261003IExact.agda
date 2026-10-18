{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003IExact where

------------------------------------------------------------------------
-- FINAL EVIDENCE-SIDE RECUT / OVERLAY I / 2026-10-03.
--
-- Overlay H established that the preferred cosmology route has four genuine
-- source-evidence leaves.  This file pushes two of those leaves one step closer
-- to executable source checks without weakening the trust boundary:
--
--   A1: the universal canonical B4 generator covariance is equivalent, on the
--       repository's literal generator carrier, to seven named generator
--       checks (flip0..flip3, swap01, swap12, swap23).
--
--   B2: the literal source margin N + Tail*Z < 0 can be paid by an explicit
--       two-budget certificate: Tail*Z <= budget and N + budget < 0.
--
-- A2 and B1 remain genuinely irreducible at the current source interfaces:
-- the bare R109 pair does not determine an observable evaluator, and R109
-- difference data do not determine the missing absolute additive constant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper
import DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact as A2NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact as B1NoGo

------------------------------------------------------------------------
-- A1 FINITE-GENERATOR REDUCTION.
------------------------------------------------------------------------

record SevenGeneratorSignedCovariance
    {Background Component Signed Value : Set}
    (actBackground : Hyper.HypercubicGenerator → Background → Background)
    (actSigned : Hyper.HypercubicGenerator → Component → Signed)
    (signedReadout : Background → Signed → Value)
    (readout : Background → Component → Value)
    : Set₁ where
  field
    flip0Covariant : ∀ background component →
      signedReadout
        (actBackground Hyper.flip0 background)
        (actSigned Hyper.flip0 component)
      ≡ readout background component

    flip1Covariant : ∀ background component →
      signedReadout
        (actBackground Hyper.flip1 background)
        (actSigned Hyper.flip1 component)
      ≡ readout background component

    flip2Covariant : ∀ background component →
      signedReadout
        (actBackground Hyper.flip2 background)
        (actSigned Hyper.flip2 component)
      ≡ readout background component

    flip3Covariant : ∀ background component →
      signedReadout
        (actBackground Hyper.flip3 background)
        (actSigned Hyper.flip3 component)
      ≡ readout background component

    swap01Covariant : ∀ background component →
      signedReadout
        (actBackground Hyper.swap01 background)
        (actSigned Hyper.swap01 component)
      ≡ readout background component

    swap12Covariant : ∀ background component →
      signedReadout
        (actBackground Hyper.swap12 background)
        (actSigned Hyper.swap12 component)
      ≡ readout background component

    swap23Covariant : ∀ background component →
      signedReadout
        (actBackground Hyper.swap23 background)
        (actSigned Hyper.swap23 component)
      ≡ readout background component

open SevenGeneratorSignedCovariance public

allLiteralGeneratorsCovariant :
  ∀ {Background Component Signed Value}
    {actBackground : Hyper.HypercubicGenerator → Background → Background}
    {actSigned : Hyper.HypercubicGenerator → Component → Signed}
    {signedReadout : Background → Signed → Value}
    {readout : Background → Component → Value} →
  SevenGeneratorSignedCovariance
    actBackground actSigned signedReadout readout →
  ∀ generator background component →
  signedReadout
    (actBackground generator background)
    (actSigned generator component)
  ≡ readout background component
allLiteralGeneratorsCovariant checks Hyper.flip0 = flip0Covariant checks
allLiteralGeneratorsCovariant checks Hyper.flip1 = flip1Covariant checks
allLiteralGeneratorsCovariant checks Hyper.flip2 = flip2Covariant checks
allLiteralGeneratorsCovariant checks Hyper.flip3 = flip3Covariant checks
allLiteralGeneratorsCovariant checks Hyper.swap01 = swap01Covariant checks
allLiteralGeneratorsCovariant checks Hyper.swap12 = swap12Covariant checks
allLiteralGeneratorsCovariant checks Hyper.swap23 = swap23Covariant checks

a1LiteralGeneratorCheckCount : Nat
a1LiteralGeneratorCheckCount = 7

a1CanonicalB4CovarianceReducesToSevenGeneratorChecks : Bool
a1CanonicalB4CovarianceReducesToSevenGeneratorChecks = true

------------------------------------------------------------------------
-- B2 SOURCE/TAIL BUDGET SPLIT.
--
-- The source evaluator can attack N and the already-explicit R109 tail product
-- separately.  No sign is inferred here: both inequalities are genuine
-- numerical/source evidence and the theorem merely composes them.
------------------------------------------------------------------------

sourceAndTailBudgetForceNegativeMargin :
  ∀ {source tailTimesPartition budget : ℚ} →
  tailTimesPartition ≤ budget →
  source + budget < 0ℚ →
  source + tailTimesPartition < 0ℚ
sourceAndTailBudgetForceNegativeMargin tailBelowBudget sourceBudgetNegative =
  ℚP.≤-<-trans
    (ℚP.+-mono-≤ ℚP.≤-refl tailBelowBudget)
    sourceBudgetNegative

record SourceTailBudgetCertificate
    (source tailTimesPartition : ℚ) : Set where
  field
    budget : ℚ
    tailProductBelowBudget : tailTimesPartition ≤ budget
    sourcePlusBudgetNegative : source + budget < 0ℚ

open SourceTailBudgetCertificate public

sourceTailBudgetCertificateForcesNegativeMargin :
  ∀ {source tailTimesPartition} →
  SourceTailBudgetCertificate source tailTimesPartition →
  source + tailTimesPartition < 0ℚ
sourceTailBudgetCertificateForcesNegativeMargin certificate =
  sourceAndTailBudgetForceNegativeMargin
    (tailProductBelowBudget certificate)
    (sourcePlusBudgetNegative certificate)

b2SourceMarginHasTwoBudgetCompiler : Bool
b2SourceMarginHasTwoBudgetCompiler = true

------------------------------------------------------------------------
-- THE TWO OTHER LEAVES ARE STILL SOURCE INFORMATION, NOT COMPILER DEBT.
------------------------------------------------------------------------

a2RemainsOneSelectedSemanticsLeaf : Bool
a2RemainsOneSelectedSemanticsLeaf =
  A2NoGo.remainingE2E4LeafIsSourceSemanticsEvaluator

b1RemainsOneAbsoluteDirectTailLeaf : Bool
b1RemainsOneAbsoluteDirectTailLeaf =
  B1NoGo.absoluteExpectationAnchorIsGenuineAdditionalInformation

preferredEvidenceLeafCount : Nat
preferredEvidenceLeafCount = 4
