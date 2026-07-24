module DASHI.Physics.Closure.NSPeriodicZeroChartDiffuseSelection where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact constructive selection reduction for all-data coverage.
--
-- The important distinction is retained: non-diffuse only supplies a large
-- packet.  It does not automatically supply Gamma alignment, off-packet tail
-- control, or the size bound.  A large packet must either produce a fully
-- admissible chart or enter a separate direct-BKM controlled branch.
------------------------------------------------------------------------

record PeriodicZeroChartDiffuseSelectionInputs
    {i : Level}
    (State Shell : Set i) : Set (lsuc i) where
  field
    ZeroState NonzeroState : State → Set i
    DiffuseState NondiffuseState : State → Set i
    DirectBKMControlled : State → Set i

    LargePacket : Shell → State → Set i
    ChartAdmissible : Shell → State → Set i

    zeroOrNonzero : ∀ u → ZeroState u ⊎ NonzeroState u

    nonzeroDiffuseOrNondiffuse : ∀ u →
      NonzeroState u →
      DiffuseState u ⊎ NondiffuseState u

    nondiffuseHasLargePacket : ∀ u →
      NondiffuseState u →
      Σ Shell (λ shell → LargePacket shell u)

    largePacketGivesChartOrDirectControl : ∀ shell u →
      LargePacket shell u →
      ChartAdmissible shell u ⊎ DirectBKMControlled u

open PeriodicZeroChartDiffuseSelectionInputs public

data PeriodicCoverageClass
    {i : Level}
    {State Shell : Set i}
    (S : PeriodicZeroChartDiffuseSelectionInputs State Shell)
    (u : State) : Set i where
  zeroCoverage :
    ZeroState S u →
    PeriodicCoverageClass S u

  chartCoverage :
    (shell : Shell) →
    ChartAdmissible S shell u →
    PeriodicCoverageClass S u

  diffuseCoverage :
    DiffuseState S u →
    PeriodicCoverageClass S u

  directBKMCoverage :
    DirectBKMControlled S u →
    PeriodicCoverageClass S u

periodicZeroChartDiffuseSelection :
  ∀ {i} {State Shell : Set i} →
  (S : PeriodicZeroChartDiffuseSelectionInputs State Shell) →
  ∀ u → PeriodicCoverageClass S u
periodicZeroChartDiffuseSelection S u with zeroOrNonzero S u
... | inj₁ zero = zeroCoverage zero
... | inj₂ nonzero with nonzeroDiffuseOrNondiffuse S u nonzero
...   | inj₁ diffuse = diffuseCoverage diffuse
...   | inj₂ nondiffuse with nondiffuseHasLargePacket S u nondiffuse
...     | shell , large with largePacketGivesChartOrDirectControl S shell u large
...       | inj₁ chart = chartCoverage shell chart
...       | inj₂ direct = directBKMCoverage direct

periodicCoverageClassAsDisjunction :
  ∀ {i} {State Shell : Set i} →
  (S : PeriodicZeroChartDiffuseSelectionInputs State Shell) →
  ∀ u →
  ZeroState S u
  ⊎ (Σ Shell (λ shell → ChartAdmissible S shell u)
  ⊎ (DiffuseState S u ⊎ DirectBKMControlled S u))
periodicCoverageClassAsDisjunction S u
  with periodicZeroChartDiffuseSelection S u
... | zeroCoverage zero = inj₁ zero
... | chartCoverage shell chart = inj₂ (inj₁ (shell , chart))
... | diffuseCoverage diffuse = inj₂ (inj₂ (inj₁ diffuse))
... | directBKMCoverage direct = inj₂ (inj₂ (inj₂ direct))

------------------------------------------------------------------------
-- Status: the constructive coverage reduction is checked.  The frontier
-- selection theorem is now exactly largePacketGivesChartOrDirectControl:
-- failure of Gamma/tail/size admissibility must itself yield direct BKM
-- control rather than being silently identified with a chart.
------------------------------------------------------------------------

zeroChartDiffuseSelectionAssemblyLevel : ProofLevel
zeroChartDiffuseSelectionAssemblyLevel = machineChecked
