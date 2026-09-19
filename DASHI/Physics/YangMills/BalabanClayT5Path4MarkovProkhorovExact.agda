{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5Path4MarkovProkhorovExact where

------------------------------------------------------------------------
-- LITERAL PATH4 GAUGE ENERGY -> UNIFORM TIGHTNESS -> PROKHOROV INPUT
--
-- This is the physical specialization of the selected Markov compactness lane.
-- The nonnegativity and coercivity of the literal Path4 gauge-energy observable
-- are already machine theorems.  The only remaining Markov-side physical seam
-- is that the selected T5 expectation is the probability integral of the same
-- pointwise observable semantics, together with admissible compact sublevels.
------------------------------------------------------------------------

open import Data.Rational using (ℚ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Realization
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyMarkovBridgeExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov

record Path4MarkovProkhorovInputs
    (Measure Observable Configuration Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ)
    (realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData) : Set₁ where
  field
    convergence : Selected.SequentialConvergence Measure

    containment :
      Path4.Path4SelectedMomentContainmentInputs
        Measure Observable Configuration Epsilon Witness
        expectationData realization

open Path4MarkovProkhorovInputs public

path4SelectedContainment :
  ∀ {Measure Observable Configuration Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    {realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData} →
  Path4MarkovProkhorovInputs
    Measure Observable Configuration Epsilon Witness expectationData realization →
  Moment.SelectedMomentCompactContainmentInputs
    Measure Observable ℚ Epsilon Witness expectationData
path4SelectedContainment inputs =
  Path4.compilePath4MomentCompactContainmentInputs (containment inputs)

path4UniformTightness :
  ∀ {Measure Observable Configuration Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    {realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData}
    (inputs :
      Path4MarkovProkhorovInputs
        Measure Observable Configuration Epsilon Witness
        expectationData realization) →
  Uniform.UniformTightnessCertificate
    Measure Epsilon Witness
    (Moment.Admissible (path4SelectedContainment inputs))
    (Moment.Controls (path4SelectedContainment inputs))
    (T5.diagonalMeasure expectationData)
path4UniformTightness inputs =
  Moment.selectedDiagonalUniformTightnessCertificate
    (path4SelectedContainment inputs)

compilePath4ProkhorovTightness :
  ∀ {Measure Observable Configuration Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    {realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData} →
  Path4MarkovProkhorovInputs
    Measure Observable Configuration Epsilon Witness expectationData realization →
  Prokhorov.SelectedSubsequenceTightnessData Measure
compilePath4ProkhorovTightness
  {expectationData = expectationData} inputs = record
  { convergence = convergence inputs
  ; sequence = T5.diagonalMeasure expectationData
  ; TightMeasureSequence =
      Uniform.UniformTightnessCertificate
        _ _ _
        (Moment.Admissible (path4SelectedContainment inputs))
        (Moment.Controls (path4SelectedContainment inputs))
  ; everyLiteralSubsequenceTight = λ subsequence →
      Uniform.restrictUniformTightnessToSubsequence
        (path4UniformTightness inputs)
        subsequence
  }

path4GaugeEnergyToUniformTightnessCompilerLevel : ProofLevel
path4GaugeEnergyToUniformTightnessCompilerLevel = machineChecked

path4UniformTightnessToProkhorovCompilerLevel : ProofLevel
path4UniformTightnessToProkhorovCompilerLevel = machineChecked

path4GaugeEnergyNonnegativeAndCoerciveLevel : ProofLevel
path4GaugeEnergyNonnegativeAndCoerciveLevel = machineChecked

-- This is now the sharp physical Markov seam on the Path4 route.
path4SelectedExpectationProbabilityIntegralSemanticsLevel : ProofLevel
path4SelectedExpectationProbabilityIntegralSemanticsLevel = conditional

path4CompactSublevelAdmissibilityLevel : ProofLevel
path4CompactSublevelAdmissibilityLevel = conditional
