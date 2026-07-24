module DASHI.Physics.Closure.NSPeriodicExtendedCoverageBKM where

open import Agda.Primitive using (Level; lsuc)

import DASHI.Physics.Closure.NSPeriodicZeroChartDiffuseSelection as Selection
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Four-branch all-state BKM assembly.
--
-- Chart failure is not renamed "diffuse".  The selection theorem may instead
-- return a separate direct-BKM controlled branch, and all four branches are
-- mapped to the same vorticity-control endpoint.
------------------------------------------------------------------------

record PeriodicExtendedCoverageBKMInputs
    {i : Level}
    {State Shell : Set i}
    (S : Selection.PeriodicZeroChartDiffuseSelectionInputs State Shell) :
    Set (lsuc i) where
  field
    VorticityControlled : State → Set i

    zeroGivesVorticityControl : ∀ u →
      Selection.ZeroState S u →
      VorticityControlled u

    chartGivesVorticityControl : ∀ shell u →
      Selection.ChartAdmissible S shell u →
      VorticityControlled u

    diffuseGivesVorticityControl : ∀ u →
      Selection.DiffuseState S u →
      VorticityControlled u

    directBKMGivesVorticityControl : ∀ u →
      Selection.DirectBKMControlled S u →
      VorticityControlled u

open PeriodicExtendedCoverageBKMInputs public

periodicExtendedCoverageGivesVorticityControl :
  ∀ {i} {State Shell : Set i}
    {S : Selection.PeriodicZeroChartDiffuseSelectionInputs State Shell} →
  (B : PeriodicExtendedCoverageBKMInputs S) →
  ∀ u → VorticityControlled B u
periodicExtendedCoverageGivesVorticityControl {S = S} B u
  with Selection.periodicZeroChartDiffuseSelection S u
... | Selection.zeroCoverage zero =
  zeroGivesVorticityControl B u zero
... | Selection.chartCoverage shell chart =
  chartGivesVorticityControl B shell u chart
... | Selection.diffuseCoverage diffuse =
  diffuseGivesVorticityControl B u diffuse
... | Selection.directBKMCoverage direct =
  directBKMGivesVorticityControl B u direct

------------------------------------------------------------------------
-- Status: the four-way coverage endpoint is checked.  The analytic frontier is
-- the large-packet chart-or-direct-control theorem and the two nontrivial BKM
-- branch estimates.
------------------------------------------------------------------------

extendedCoverageBKMAssemblyLevel : ProofLevel
extendedCoverageBKMAssemblyLevel = machineChecked
