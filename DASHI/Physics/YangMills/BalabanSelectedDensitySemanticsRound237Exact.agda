{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedDensitySemanticsRound237Exact where

------------------------------------------------------------------------
-- ROUND237 / THE PREFERRED CONSUMER DOES NOT NEED A TOTAL DENSITY INTERPRETER
--
-- R213 correctly source-fixes a total `Density -> potential` map, but the
-- preferred finite-cutoff continuation only reads the selected sequence
-- `densityAt inputs scale`.  Requiring semantics for arbitrary Density values is
-- therefore stronger than the consumer contract.
--
-- This source-fixed selected semantics is indexed by scale.  Its provenance
-- predicate is fixed independently of any BC1 target; the record cannot certify
-- a chosen target merely by defining the predicate after the fact.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow

record SelectedEffectiveDensitySemantics
    {trajectory split}
    (inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}) : Set₁ where
  field
    Background : Set

    selectedPotential : Nat → Background → ℝ

    IsSourceMeaningOfSelectedDensity :
      Nat → (Background → ℝ) → Set

    selectedPotentialHasSourceMeaning : ∀ scale →
      IsSourceMeaningOfSelectedDensity scale (selectedPotential scale)

open SelectedEffectiveDensitySemantics public

selectedDensitySemanticsCompilerLevel : ProofLevel
selectedDensitySemanticsCompilerLevel = machineChecked

-- Least-privilege source leaf: instantiate the selected finite-scale potential
-- semantics and its source-authority predicate for the literal CMP119/CMP122
-- density sequence.  No semantics for unconsumed arbitrary Density values is
-- required on the preferred route.
literalSelectedCMP119DensitySemanticsLevel : ProofLevel
literalSelectedCMP119DensitySemanticsLevel = conditional
