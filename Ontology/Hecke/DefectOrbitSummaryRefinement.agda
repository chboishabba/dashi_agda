module Ontology.Hecke.DefectOrbitSummaryRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedOrbitSummaryP2At
    )
open import Ontology.Hecke.CurrentSaturatedOrbitSummaryCollapse
  using
    ( canonicalSaturatedOrbitSummary
    ; saturatedOrbitSummary≡canonical
    )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
  using (DefectOrbitSummary)

------------------------------------------------------------------------
-- Minimal refinement above the current orbit-summary scalar.
--
-- The current saturated branch already collapses at the full
-- `DefectOrbitSummary` level, so this module does not pretend to discover a
-- new separator on that branch.  It packages the smallest histogram-style
-- refinement sitting above the scalar field:
--
--   stableCount  = forcedStableCount
--   illegalCount = motif / repatterning / contractive / expansive activity
--   otherCount   = totalDrift
--
-- On the current saturated branch this histogram also collapses.  That is the
-- actual theorem. Any further split, such as a candidate `9 + 6`
-- decomposition, must therefore live strictly above this histogram package.

record DefectHistogram : Set where
  constructor defectHistogram
  field
    stableCount : Nat
    illegalCount : Nat
    otherCount : Nat

open DefectHistogram public

orbitSummaryHistogram : DefectOrbitSummary → DefectHistogram
orbitSummaryHistogram s =
  defectHistogram
    (FOS.DefectOrbitSummary.forcedStableCount s)
    (  FOS.DefectOrbitSummary.motifChangeCount s
     + FOS.DefectOrbitSummary.repatterningCount s
     + FOS.DefectOrbitSummary.contractiveCount s
     + FOS.DefectOrbitSummary.expansiveCount s)
    (FOS.DefectOrbitSummary.totalDrift s)

forcedStable-factors-through-histogram :
  ∀ s →
  FOS.DefectOrbitSummary.forcedStableCount s
    ≡
  stableCount (orbitSummaryHistogram s)
forcedStable-factors-through-histogram _ = refl

canonicalSaturatedHistogram : DefectHistogram
canonicalSaturatedHistogram = defectHistogram 15 zero zero

canonicalSaturatedHistogram-law :
  orbitSummaryHistogram canonicalSaturatedOrbitSummary ≡ canonicalSaturatedHistogram
canonicalSaturatedHistogram-law = refl

saturatedHistogramAt : CurrentSaturatedGenerator → DefectHistogram
saturatedHistogramAt c = orbitSummaryHistogram (saturatedOrbitSummaryP2At c)

saturatedHistogram≡canonical :
  ∀ c →
  saturatedHistogramAt c ≡ canonicalSaturatedHistogram
saturatedHistogram≡canonical c
  rewrite saturatedOrbitSummary≡canonical c = canonicalSaturatedHistogram-law
