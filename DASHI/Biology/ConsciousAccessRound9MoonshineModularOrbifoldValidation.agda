module DASHI.Biology.ConsciousAccessRound9MoonshineModularOrbifoldValidation where

------------------------------------------------------------------------
-- Cumulative Round-Nine validation root.
--
-- Imports the Round-Eight VOA grade semantics and the exact modular-form,
-- Z/2 projector, modular-sector, Monster-Lie, Griess-automorphism and route
-- comparison modules without opening colliding domain names.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.ConsciousAccessRound8VOAGradeSemanticsValidation
import DASHI.Biology.MoonshineModularFormCoefficientExact
import DASHI.Biology.MoonshineOrbifoldSectorProjectorExact
import DASHI.Biology.MoonshineOrbifoldModularSectorActionExact
import DASHI.Biology.MoonshineMonsterLieStringBigradingExact
import DASHI.Biology.MoonshineGriessAutomorphismClassificationExact
import DASHI.Biology.MonsterConstructionRouteComparisonExact

round9MoonshineModularOrbifoldRoot : Set
round9MoonshineModularOrbifoldRoot = ⊤

round9MoonshineModularOrbifoldRootInhabited :
  round9MoonshineModularOrbifoldRoot
round9MoonshineModularOrbifoldRootInhabited = tt

round9MoonshineModularOrbifoldRootStable :
  round9MoonshineModularOrbifoldRoot ≡ ⊤
round9MoonshineModularOrbifoldRootStable = refl
