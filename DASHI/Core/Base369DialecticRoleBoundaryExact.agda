module DASHI.Core.Base369DialecticRoleBoundaryExact where

------------------------------------------------------------------------
-- BASE369 / DIALECTIC / MOTIF ROLE BOUNDARY
--
-- Existing repo owners already distinguish several numeral roles.  In
-- particular Base369 provides TriTruth/HexTruth/NonaryTruth arithmetic, while
-- Base369NumeralOntologyBoundary separates those algebraic carriers from UFT
-- traversal addresses and prime-coordinate boundaries.
--
-- The recovered historical notes add two more distinct uses of the same
-- printed numerals: dialectical roles (3 = distinction, 6 = relation/tension,
-- 9 = closure) and later motif labels M3/M6/M9.  This module prevents those
-- roles from being silently identified.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.Base369NumeralOntologyBoundary as Existing
import DASHI.Core.DialecticalStageSpectrumExact as Stage
import DASHI.Reasoning.DialecticMotifKernel as Motif

------------------------------------------------------------------------
-- Typed role tags.
------------------------------------------------------------------------

data ThreeSixNineRole : Set where
  arithmeticCarrierRole
  historicalDialecticRole
  stageIndexRole
  operationalMotifRole
  traversalControlRole
  : ThreeSixNineRole

arithmetic≠dialectic : arithmeticCarrierRole ≡ historicalDialecticRole → ⊥
arithmetic≠dialectic ()

dialectic≠motif : historicalDialecticRole ≡ operationalMotifRole → ⊥
dialectic≠motif ()

stage≠motif : stageIndexRole ≡ operationalMotifRole → ⊥
stage≠motif ()

arithmetic≠traversal : arithmeticCarrierRole ≡ traversalControlRole → ⊥
arithmetic≠traversal ()

------------------------------------------------------------------------
-- Concrete existing-carrier witnesses.
------------------------------------------------------------------------

triCarrier : Set
triCarrier = Base.TriTruth

hexCarrier : Set
hexCarrier = Base.HexTruth

nonaryCarrier : Set
nonaryCarrier = Base.NonaryTruth

existingAlgebraicRoleIsBase369 :
  Existing.AlgebraicCarrierRole.triCarrier Existing.base369AlgebraicCarrierRole
  ≡ Base.TriTruth
existingAlgebraicRoleIsBase369 = refl

stage6IndexIsSix : Stage.stageIndex Stage.stage6 ≡ 6
stage6IndexIsSix = refl

motifM6PolicyIsRedesign : Motif.policy Motif.M6 ≡ Motif.redesign
motifM6PolicyIsRedesign = refl

stage9IndexIsNine : Stage.stageIndex Stage.stage9 ≡ 9
stage9IndexIsNine = refl

motifM9PolicyIsProhibit : Motif.policy Motif.M9 ≡ Motif.prohibit
motifM9PolicyIsProhibit = refl

------------------------------------------------------------------------
-- Historical semantic roles are annotations, not algebraic definitions.
------------------------------------------------------------------------

data Dialectic369Role : Set where
  distinctionRole relationOrTensionRole closureRole : Dialectic369Role

historicalRole : Nat → Dialectic369Role
historicalRole 3 = distinctionRole
historicalRole 6 = relationOrTensionRole
historicalRole _ = closureRole

threeHistoricalRole : historicalRole 3 ≡ distinctionRole
threeHistoricalRole = refl

sixHistoricalRole : historicalRole 6 ≡ relationOrTensionRole
sixHistoricalRole = refl

nineHistoricalRole : historicalRole 9 ≡ closureRole
nineHistoricalRole = refl

record Base369DialecticRoleBoundary : Set where
  constructor base369-dialectic-role-boundary
  field
    M6IsHexTruthDefinition : Bool
    M6IsHexTruthDefinitionIsFalse : M6IsHexTruthDefinition ≡ false
    M9IsNonaryTruthDefinition : Bool
    M9IsNonaryTruthDefinitionIsFalse : M9IsNonaryTruthDefinition ≡ false
    stage6IsHexadicCarrier : Bool
    stage6IsHexadicCarrierIsFalse : stage6IsHexadicCarrier ≡ false
    historicalClosureRoleIsNonaryRingTheorem : Bool
    historicalClosureRoleIsNonaryRingTheoremIsFalse :
      historicalClosureRoleIsNonaryRingTheorem ≡ false
    samePrintedNumeralImpliesSameTypedRole : Bool
    samePrintedNumeralImpliesSameTypedRoleIsFalse :
      samePrintedNumeralImpliesSameTypedRole ≡ false

canonicalBase369DialecticRoleBoundary : Base369DialecticRoleBoundary
canonicalBase369DialecticRoleBoundary =
  base369-dialectic-role-boundary
    false refl false refl false refl false refl false refl
