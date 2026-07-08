module DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero)

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation

------------------------------------------------------------------------
-- Upstream actual repeated-pair kernel formula surface.
--
-- The receipt layer already records the scripted identity
--
--   K_N(k , p) = - L_FT,script^N(k , p)
--
-- as a repeated-pair incidence sum over retained positive-sector triad
-- weights. Blocker 2A now needs this formula exported as typed data rather
-- than prose/receipt authority. But that formula itself is downstream of a
-- unified actual repeated-pair incidence relation, which the current repo
-- still does not export.

record ActualPairIncidenceKernelFormulaData
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkActualPairIncidenceKernelFormulaData
  field
    FiniteIndex : Set
    TailIndex : Set

    actualKernel : FiniteIndex → TailIndex → Nat

    triadWeight : FiniteIndex → TailIndex → Nat

    repeatedPairIncidenceFormula : Set
    nonnegativeKernelWitness : Set

open ActualPairIncidenceKernelFormulaData public

UnitShellActualPairIncidenceKernelFormulaDataTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
UnitShellActualPairIncidenceKernelFormulaDataTarget residueNormModel =
  ActualPairIncidenceKernelFormulaData residueNormModel (suc zero)

actualPairIncidenceKernelFormulaDataClosed : Bool
actualPairIncidenceKernelFormulaDataClosed =
  Relation.actualPairIncidenceRelationDataClosed

actualPairIncidenceKernelFormulaDataClosedIsFalse :
  actualPairIncidenceKernelFormulaDataClosed ≡ false
actualPairIncidenceKernelFormulaDataClosedIsFalse =
  Relation.actualPairIncidenceRelationDataClosedIsFalse

actualUnitShellPairIncidenceKernelFormulaDataClosed : Bool
actualUnitShellPairIncidenceKernelFormulaDataClosed =
  Relation.actualUnitShellPairIncidenceRelationDataClosed

actualUnitShellPairIncidenceKernelFormulaDataClosedIsFalse :
  actualUnitShellPairIncidenceKernelFormulaDataClosed ≡ false
actualUnitShellPairIncidenceKernelFormulaDataClosedIsFalse =
  Relation.actualUnitShellPairIncidenceRelationDataClosedIsFalse
