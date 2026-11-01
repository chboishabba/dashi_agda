module Ontology.Hecke.CurrentSaturatedOrbitSummaryCollapse where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedAnchoredTrajectory
    ; saturatedBalancedComposed
    ; saturatedBalancedCycle
    ; saturatedDenseComposed
    ; saturatedExplicitWidth2
    ; saturatedExplicitWidth3
    ; saturatedFullSupportCascade
    ; saturatedGeneratorClass
    ; saturatedOrbitSummaryP2At
    ; saturatedSupportCascade
    )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
  using
    ( DefectOrbitSummary
    ; defectOrbitSummary
    )

------------------------------------------------------------------------
-- Stronger current negative boundary on the saturated side.
--
-- The present all-generator saturated branch does not merely collapse at the
-- `forcedStableCount` field.  On the current taxonomy it already collapses at
-- the full `DefectOrbitSummary` level to the fully stable `p2` summary.

canonicalSaturatedOrbitSummary : DefectOrbitSummary
canonicalSaturatedOrbitSummary =
  defectOrbitSummary 15 zero zero zero zero zero

saturatedOrbitSummary≡canonical :
  ∀ c →
  saturatedOrbitSummaryP2At c ≡ canonicalSaturatedOrbitSummary
saturatedOrbitSummary≡canonical saturatedExplicitWidth3 = refl
saturatedOrbitSummary≡canonical saturatedDenseComposed = refl
saturatedOrbitSummary≡canonical saturatedBalancedCycle = refl
saturatedOrbitSummary≡canonical saturatedBalancedComposed = refl
saturatedOrbitSummary≡canonical saturatedExplicitWidth2 = refl
saturatedOrbitSummary≡canonical saturatedAnchoredTrajectory = refl
saturatedOrbitSummary≡canonical saturatedSupportCascade = refl
saturatedOrbitSummary≡canonical saturatedFullSupportCascade = refl
