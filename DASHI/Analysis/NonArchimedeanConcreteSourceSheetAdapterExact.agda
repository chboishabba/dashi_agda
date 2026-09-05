module DASHI.Analysis.NonArchimedeanConcreteSourceSheetAdapterExact where

------------------------------------------------------------------------
-- SINGLE CONCRETE SOURCE ADAPTER
--
-- This is the only remaining foreign-source instantiation point for the finite
-- spectral core.  It packages the exact checked Lean ingredients from
-- `CollatzRelMatrix.lean` into the already-owned DASHI twisted restriction
-- compiler.
--
-- Required Lean-side ingredients:
--   * `D'_matrix` with sheets 0 and 1;
--   * `D'_tau_sym_diag`;
--   * `D'_tau_sym_offdiag`;
--   * `twistedDirMatrix = sheet00 - sheet01` by definition;
--   * binary exhaustivity of `ZMod 2` (the source already uses `fin_cases`).
--
-- Once an instance of `sourceRestrictionData` is supplied, the Core.Intertwiner
-- receipt and all character/DFT consumers are downstream compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.NonArchimedeanTwistedRestrictionIntertwinerExact as Restrict
import DASHI.Analysis.NonArchimedeanTwistedRestrictionCoreIntertwinerExact as CoreReuse
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core

record ConcreteSourceSheetAdapter : Set₁ where
  field
    sourceRestrictionData : Restrict.TwistedRestrictionData

    sourceUsesTwoSheets : Bool
    sourceSheetZeroOneExhaustive : Bool
    sourceDiagonalTauSymmetryOwned : Bool
    sourceOffDiagonalTauSymmetryOwned : Bool
    sourceTwistedBlockIsSheetDifference : Bool

open ConcreteSourceSheetAdapter public

compiledSourceTwistedIntertwiner :
  (adapter : ConcreteSourceSheetAdapter) →
  Core.Intertwiner
    (Restrict.extendMinus (sourceRestrictionData adapter))
    (Restrict.extendMinus (sourceRestrictionData adapter))
    (Restrict.twistedStep (sourceRestrictionData adapter))
    (Restrict.fullStep (sourceRestrictionData adapter))
compiledSourceTwistedIntertwiner adapter =
  CoreReuse.coreTwistedRestrictionIntertwiner
    (sourceRestrictionData adapter)

record ConcreteAdapterBoundary : Set where
  constructor concreteAdapterBoundary
  field
    newGenericMathematicsRequired : Bool
    newFourierTheoryRequired : Bool
    newOrbitTheoryRequired : Bool
    sourceDefinitionInstantiationRequired : Bool
    oneAdapterFeedsAllSpatialConsumers : Bool

canonicalConcreteAdapterBoundary : ConcreteAdapterBoundary
canonicalConcreteAdapterBoundary =
  concreteAdapterBoundary false false false true true

onlyForeignInstantiationRemains :
  ConcreteAdapterBoundary.sourceDefinitionInstantiationRequired
    canonicalConcreteAdapterBoundary
  ≡ true
onlyForeignInstantiationRemains = refl
