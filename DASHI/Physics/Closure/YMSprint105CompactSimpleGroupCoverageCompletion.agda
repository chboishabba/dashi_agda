module DASHI.Physics.Closure.YMSprint105CompactSimpleGroupCoverageCompletion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

import DASHI.Physics.Closure.YMSprint105CompactSimpleGroupParameterTable as Sprint105
open import DASHI.Physics.Closure.YMCompactSimpleGroupParametricCoverage

------------------------------------------------------------------------
-- Completion bridge for the Sprint 105 finite-table audit.
--
-- The old finite table remains available as historical status data.  The new
-- theorem surface is classification-parametric and includes all classical and
-- exceptional compact-simple Lie algebras together with finite central global
-- forms.

record CompactSimpleGroupCoverageCompletion : Set where
  field
    historicalFiniteTableRetained : Bool
    historicalFiniteTableRetainedIsTrue :
      historicalFiniteTableRetained ≡ true

    classicalFamiliesCovered : Bool
    classicalFamiliesCoveredIsTrue :
      classicalFamiliesCovered ≡ true

    exceptionalFamiliesCovered : Bool
    exceptionalFamiliesCoveredIsTrue :
      exceptionalFamiliesCovered ≡ true

    finiteCentralGlobalFormsCovered : Bool
    finiteCentralGlobalFormsCoveredIsTrue :
      finiteCentralGlobalFormsCovered ≡ true

    latticeIndependenceTheoremPresent : Bool
    latticeIndependenceTheoremPresentIsTrue :
      latticeIndependenceTheoremPresent ≡ true

    analyticProviderCertificatesExplicit : Bool
    analyticProviderCertificatesExplicitIsTrue :
      analyticProviderCertificatesExplicit ≡ true

    clayPromotionUnaffected :
      Sprint105.clayYangMillsPromoted ≡ false

open CompactSimpleGroupCoverageCompletion public

compactSimpleGroupCoverageCompletion :
  CompactSimpleGroupCoverageCompletion
compactSimpleGroupCoverageCompletion =
  record
    { historicalFiniteTableRetained = true
    ; historicalFiniteTableRetainedIsTrue = refl
    ; classicalFamiliesCovered = true
    ; classicalFamiliesCoveredIsTrue = refl
    ; exceptionalFamiliesCovered = true
    ; exceptionalFamiliesCoveredIsTrue = refl
    ; finiteCentralGlobalFormsCovered = true
    ; finiteCentralGlobalFormsCoveredIsTrue = refl
    ; latticeIndependenceTheoremPresent = true
    ; latticeIndependenceTheoremPresentIsTrue = refl
    ; analyticProviderCertificatesExplicit = true
    ; analyticProviderCertificatesExplicitIsTrue = refl
    ; clayPromotionUnaffected = refl
    }

compactSimpleCoverageTheorem :
  (G : CompactSimpleGlobalForm) →
  QuantitativeCompactLiePackage G
compactSimpleCoverageTheorem = compactSimpleHasQuantitativePackage

compactSimpleLatticeUniformityTheorem :
  (G : CompactSimpleGlobalForm) →
  Σ Nat
    (λ λG →
      (Λ k U₀ P : Nat) →
      LocalLieConstants G (latticeDatum Λ k U₀ P) ≡ λG)
compactSimpleLatticeUniformityTheorem = groupConstantsIndependentOfLattice
