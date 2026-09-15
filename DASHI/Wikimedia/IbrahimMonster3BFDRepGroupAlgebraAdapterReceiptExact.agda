module DASHI.Wikimedia.IbrahimMonster3BFDRepGroupAlgebraAdapterReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- LEAN FDREP -> GROUP-ALGEBRA ADAPTER RECEIPT
--
-- A small source-level adapter now exists in dashi_lean4.  It records the
-- canonical same-action equation inherited from mathlib:
--
--   V.ρ.asModuleEquiv.symm (V.ρ g x)
--     = MonoidAlgebra.of k G g • V.ρ.asModuleEquiv.symm x.
--
-- This pays only the representation-to-module action seam.  It does NOT yet
-- prove that whole-character equality forces one isotypic type, and source
-- presence is kept separate from kernel execution / Agda transport.
------------------------------------------------------------------------

record LeanFDRepGroupAlgebraAdapterReceipt : Set where
  constructor lean-fdrep-group-algebra-adapter-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    regressionPath : String
    theoremName : String
    redCommit : String
    sourceCommit : String
    rootIntegrationCommit : String
open LeanFDRepGroupAlgebraAdapterReceipt public

currentLeanFDRepGroupAlgebraAdapterReceipt : LeanFDRepGroupAlgebraAdapterReceipt
currentLeanFDRepGroupAlgebraAdapterReceipt =
  lean-fdrep-group-algebra-adapter-receipt
    "chboishabba/dashi_lean4"
    "agent/monster3b-fdrep-groupalgebra-adapter"
    "Synthesis/MonsterWholeCharacterModuleAdapter.lean"
    "Synthesis/MonsterWholeCharacterModuleAdapterRegression.lean"
    "Synthesis.fdrep_asModule_action_bridge"
    "593e23fbce3b254ca024d89c9c8a23baeeabf670"
    "27a37db2c54f46f4a9bfecd196217077f5f50e72"
    "d52cbc8c5b3d0a64b9d8232251248a6ccf6633b6"

------------------------------------------------------------------------
-- WrongType / certification firewalls.
------------------------------------------------------------------------

data SourcePresenceCreatesKernelReceipt : Set where
data SameActionAdapterCreatesIsotypicTheorem : Set where
data OEISCreatesAdapterTheorem : Set where

sourcePresenceDoesNotCreateKernelReceipt : SourcePresenceCreatesKernelReceipt -> ⊥
sourcePresenceDoesNotCreateKernelReceipt ()

sameActionAdapterDoesNotCreateIsotypicTheorem :
  SameActionAdapterCreatesIsotypicTheorem -> ⊥
sameActionAdapterDoesNotCreateIsotypicTheorem ()

oeisDoesNotCreateAdapterTheorem : OEISCreatesAdapterTheorem -> ⊥
oeisDoesNotCreateAdapterTheorem ()

record FDRepGroupAlgebraAdapterBoundary : Set where
  constructor fdrep-group-algebra-adapter-boundary
  field
    leanAdapterSourceWritten : Bool
    sameActionEquationWritten : Bool
    wholeCharacterToIsotypicTheoremWritten : Bool
    leanKernelReceiptObserved : Bool
    agdaTransportObserved : Bool
    oeisCreatesAdapterTheorem : Bool
    nextResidual : String
open FDRepGroupAlgebraAdapterBoundary public

canonicalFDRepGroupAlgebraAdapterBoundary : FDRepGroupAlgebraAdapterBoundary
canonicalFDRepGroupAlgebraAdapterBoundary =
  fdrep-group-algebra-adapter-boundary
    true true false false false false
    "kernel-check the exact dashi_lean4 adapter on the pinned v4.28.0 project, then use the transported same-action module view to attempt only the next consumer-sufficient theorem: derive the H_zeta isotypic class from the whole restricted character under semisimplicity/simple hypotheses. If that theorem remains expensive, reopen the literal constituent residual. OEIS and dimension identities remain non-promoting."
