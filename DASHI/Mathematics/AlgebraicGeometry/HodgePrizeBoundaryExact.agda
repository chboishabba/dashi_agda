module DASHI.Mathematics.AlgebraicGeometry.HodgePrizeBoundaryExact where

------------------------------------------------------------------------
-- PRIZE-FACING TERMINAL HODGE INTERFACE
--
-- No projective-space or finite-model theorem appears here.
--
-- The Clay statement on the repository carriers is exactly the universal
-- reopening of the actual cycle-class map:
--
--   for every actual smooth projective complex variety / comparison /
--   Hodge decomposition / actual cycle-class map / codimension,
--   every rational Hodge class has an algebraic-cycle preimage.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as H

record UniversalHodgeReopening : Setω where
  field
    reopen :
      ∀ {X : H.SmoothProjectiveComplexVariety}
        {comparison : H.SingularDeRhamComparison X}
        {hodge : H.HodgeDecomposition X comparison}
        (cycleMap : H.CycleClassMap X comparison hodge)
        (p : Nat)
        (α : H.RationalHodgeClass hodge p) →
      H.Cycle cycleMap p

    reopeningCorrect :
      ∀ {X : H.SmoothProjectiveComplexVariety}
        {comparison : H.SingularDeRhamComparison X}
        {hodge : H.HodgeDecomposition X comparison}
        (cycleMap : H.CycleClassMap X comparison hodge)
        (p : Nat)
        (α : H.RationalHodgeClass hodge p) →
      H.cycleClass cycleMap p (reopen cycleMap p α)
      ≡ H.hodgeClassValue α

open UniversalHodgeReopening public

record UniversalHodgeConjecture : Setω where
  field
    atEveryCodimension :
      ∀ {X : H.SmoothProjectiveComplexVariety}
        {comparison : H.SingularDeRhamComparison X}
        {hodge : H.HodgeDecomposition X comparison}
        (cycleMap : H.CycleClassMap X comparison hodge)
        (p : Nat) →
      H.HodgeConjectureAtCodimension cycleMap p

open UniversalHodgeConjecture public

universalReopeningImpliesHodge :
  UniversalHodgeReopening →
  UniversalHodgeConjecture
universalReopeningImpliesHodge opening = record
  { atEveryCodimension = λ cycleMap p → record
      { H.everyRationalHodgeClassHasCycle =
          reopen opening cycleMap p
      ; H.cycleRepresentsClass =
          reopeningCorrect opening cycleMap p
      }
  }

hodgeImpliesUniversalReopening :
  UniversalHodgeConjecture →
  UniversalHodgeReopening
hodgeImpliesUniversalReopening conjecture = record
  { reopen = λ cycleMap p α →
      H.everyRationalHodgeClassHasCycle
        (atEveryCodimension conjecture cycleMap p) α
  ; reopeningCorrect = λ cycleMap p α →
      H.cycleRepresentsClass
        (atEveryCodimension conjecture cycleMap p) α
  }

record HodgePrizeBoundary : Setω where
  field
    exactReopeningTarget : Setω
    targetIsUniversalReopening :
      exactReopeningTarget ≡ UniversalHodgeReopening

hodgePrizeBoundary : HodgePrizeBoundary
hodgePrizeBoundary = record
  { exactReopeningTarget = UniversalHodgeReopening
  ; targetIsUniversalReopening = refl
  }
