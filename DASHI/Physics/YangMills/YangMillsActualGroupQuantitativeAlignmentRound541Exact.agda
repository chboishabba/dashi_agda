{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeAlignmentRound541Exact where

------------------------------------------------------------------------
-- GOAL-1 / ALL-G / ROUND541:
-- THE QUANTITATIVE CLASSIFICATION PACKAGE MUST BE THE SAME ACTUAL GROUP
--
-- R517 indexes the literal Clay construction by actual proof-bearing
-- CompactSimpleLieGroup objects.
--
-- G1's quantitative lane is classified by CompactSimpleQuantitativeCoverage's
-- family tag.  Matching carrier TYPES is not enough: the quantitative exp/log,
-- bracket and adjoint must denote the structures of the same actual group.
--
-- This file makes that missing same-group bridge explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Quant
import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as R517
import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact as G1

record ActualGroupQuantitativeAlignment
    (GaugeIndex X : Set)
    (structural : R517.StructuralSourceBundle GaugeIndex X)
    : Set₂ where
  field
    classification :
      GaugeIndex → Quant.CompactSimpleLieGroup

    quantitative :
      ∀ group →
      Quant.QuantitativeCompactLiePackage
        ℚ
        (R517.LieCarrier structural group)
        (R517.GroupCarrier structural group)
        (classification group)

    bracketIsActual :
      ∀ group left right →
      Quant.bracket (quantitative group) left right
      ≡
      Core.bracket
        (Core.algebra (R517.compactSimple structural group))
        left right

    expIsActual :
      ∀ group element →
      Quant.exp (quantitative group) element
      ≡
      Core.exp
        (R517.compactSimple structural group)
        element

    logIsActual :
      ∀ group element →
      Quant.log (quantitative group) element
      ≡
      Core.log
        (R517.compactSimple structural group)
        element

    adjointIsActual :
      ∀ group groupElement lieElement →
      Quant.adjoint (quantitative group) groupElement lieElement
      ≡
      Core.Ad
        (R517.compactSimple structural group)
        groupElement lieElement

open ActualGroupQuantitativeAlignment public

record ActualGroupFiveBlockSource
    (GaugeIndex X : Set)
    (structural : R517.StructuralSourceBundle GaugeIndex X)
    (alignment :
      ActualGroupQuantitativeAlignment GaugeIndex X structural)
    : Set₂ where
  field
    fiveBlock :
      ∀ group →
      G1.GroupParametricFiveBlockG2Data
        (R517.LieCarrier structural group)
        (R517.GroupCarrier structural group)
        (classification alignment group)

    -- The quantitative package consumed by the five-block theorem is exactly
    -- the one aligned above; no second package can be chosen.
    fiveBlockQuantitativeIsAligned :
      ∀ group →
      G1.quantitativeLiePackage (fiveBlock group)
      ≡ quantitative alignment group

open ActualGroupFiveBlockSource public

round541ActualGroupAlignmentInterfaceLevel : ProofLevel
round541ActualGroupAlignmentInterfaceLevel = machineChecked

-- Genuine all-G source payment: classify each actual compact-simple group and
-- instantiate quantitative local analytic data on its actual Lie/group
-- structure, with the pointwise structure equalities above.
literalRound541ActualGroupQuantitativeAlignmentLevel : ProofLevel
literalRound541ActualGroupQuantitativeAlignmentLevel = conditional

-- The five scalar source map itself remains the independent G1 physical theorem.
literalRound541AlignedFiveBlockSourceLevel : ProofLevel
literalRound541AlignedFiveBlockSourceLevel =
  G1.physicalGroupParametricFiveBlockSourceMapLevel
