module DASHI.Physics.Closure.NSPeriodicChartFailureCoverage where

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSPeriodicZeroChartDiffuseSelection as Selection
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact expansion of the large-packet chart-selection frontier.
--
-- A large packet is a chart only when Gamma alignment, off-packet control, and
-- the size bound all hold.  Failure of any one condition must itself enter a
-- direct-BKM controlled branch.  This module performs the exhaustive finite
-- case split and constructs the selection theorem; it does not silently rename
-- a chart failure as "diffuse".
------------------------------------------------------------------------

record PeriodicChartFailureCoverageInputs
    {i : Level}
    (State Shell : Set i) : Set (lsuc i) where
  field
    LargePacket : Shell → State → Set i
    GammaGood TailGood SizeGood : Shell → State → Set i
    ChartAdmissible : Shell → State → Set i
    DirectBKMControlled : State → Set i

    gammaDecision : ∀ shell u →
      GammaGood shell u ⊎ (GammaGood shell u → ⊥)

    tailDecision : ∀ shell u →
      TailGood shell u ⊎ (TailGood shell u → ⊥)

    sizeDecision : ∀ shell u →
      SizeGood shell u ⊎ (SizeGood shell u → ⊥)

    chartFromAllConditions : ∀ shell u →
      LargePacket shell u →
      GammaGood shell u →
      TailGood shell u →
      SizeGood shell u →
      ChartAdmissible shell u

    gammaFailureGivesDirectBKM : ∀ shell u →
      LargePacket shell u →
      (GammaGood shell u → ⊥) →
      DirectBKMControlled u

    tailFailureGivesDirectBKM : ∀ shell u →
      LargePacket shell u →
      GammaGood shell u →
      (TailGood shell u → ⊥) →
      DirectBKMControlled u

    sizeFailureGivesDirectBKM : ∀ shell u →
      LargePacket shell u →
      GammaGood shell u →
      TailGood shell u →
      (SizeGood shell u → ⊥) →
      DirectBKMControlled u

open PeriodicChartFailureCoverageInputs public

largePacketGivesChartOrDirectBKM :
  ∀ {i} {State Shell : Set i} →
  (C : PeriodicChartFailureCoverageInputs State Shell) →
  ∀ shell u →
  LargePacket C shell u →
  ChartAdmissible C shell u ⊎ DirectBKMControlled C u
largePacketGivesChartOrDirectBKM C shell u large
  with gammaDecision C shell u
... | inj₂ notGamma =
  inj₂ (gammaFailureGivesDirectBKM C shell u large notGamma)
... | inj₁ gamma with tailDecision C shell u
...   | inj₂ notTail =
  inj₂ (tailFailureGivesDirectBKM C shell u large gamma notTail)
...   | inj₁ tail with sizeDecision C shell u
...     | inj₂ notSize =
  inj₂ (sizeFailureGivesDirectBKM C shell u large gamma tail notSize)
...     | inj₁ size =
  inj₁ (chartFromAllConditions C shell u large gamma tail size)

record ChartFailureSelectionAdapterInputs
    {i : Level}
    (State Shell : Set i) : Set (lsuc i) where
  field
    selectionBase :
      Selection.PeriodicZeroChartDiffuseSelectionInputs State Shell

    chartFailureInputs :
      PeriodicChartFailureCoverageInputs State Shell

    largePacketMatches : ∀ shell u →
      Selection.LargePacket selectionBase shell u →
      LargePacket chartFailureInputs shell u

    chartMatches : ∀ shell u →
      ChartAdmissible chartFailureInputs shell u →
      Selection.ChartAdmissible selectionBase shell u

    directControlMatches : ∀ u →
      DirectBKMControlled chartFailureInputs u →
      Selection.DirectBKMControlled selectionBase u

open ChartFailureSelectionAdapterInputs public

largePacketSelectionFromFailureCases :
  ∀ {i} {State Shell : Set i} →
  (A : ChartFailureSelectionAdapterInputs State Shell) →
  ∀ shell u →
  Selection.LargePacket (selectionBase A) shell u →
  Selection.ChartAdmissible (selectionBase A) shell u
  ⊎ Selection.DirectBKMControlled (selectionBase A) u
largePacketSelectionFromFailureCases A shell u large
  with largePacketGivesChartOrDirectBKM
    (chartFailureInputs A) shell u (largePacketMatches A shell u large)
... | inj₁ chart = inj₁ (chartMatches A shell u chart)
... | inj₂ direct = inj₂ (directControlMatches A u direct)

------------------------------------------------------------------------
-- Status: exhaustive classification is reduced to three explicit analytic
-- failure controls: bad Gamma, bad tail, and excessive size.  The logical
-- selection and chart construction are checked.
------------------------------------------------------------------------

chartFailureCoverageAssemblyLevel : ProofLevel
chartFailureCoverageAssemblyLevel = machineChecked
