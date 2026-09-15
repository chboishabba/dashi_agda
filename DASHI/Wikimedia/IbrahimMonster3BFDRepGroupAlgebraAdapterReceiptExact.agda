module DASHI.Wikimedia.IbrahimMonster3BFDRepGroupAlgebraAdapterReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- LEAN FDREP -> GROUP-ALGEBRA ADAPTER RECEIPT
--
-- The Lean branch now exposes two source-level adapters:
--
--   1. the canonical same-action equation
--      V.ρ.asModuleEquiv.symm (V.ρ g x)
--        = MonoidAlgebra.of k G g • V.ρ.asModuleEquiv.symm x;
--
--   2. every k[G]-submodule of V.ρ.asModule maps through asModuleEquiv to a
--      k-submodule of V stable under every V.ρ g.
--
-- This closes the object-level action/subobject interface seam only.  It does
-- NOT yet prove that whole-character equality forces one isotypic type, and
-- source presence remains separate from kernel execution / Agda transport.
------------------------------------------------------------------------

record LeanFDRepGroupAlgebraAdapterReceipt : Set where
  constructor lean-fdrep-group-algebra-adapter-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    actionRegressionPath : String
    submoduleRegressionPath : String
    actionTheoremName : String
    submoduleTheoremName : String
    actionRedCommit : String
    actionSourceCommit : String
    firstRootIntegrationCommit : String
    submoduleRedCommit : String
    submoduleSourceCommit : String
    currentRootIntegrationCommit : String
open LeanFDRepGroupAlgebraAdapterReceipt public

currentLeanFDRepGroupAlgebraAdapterReceipt : LeanFDRepGroupAlgebraAdapterReceipt
currentLeanFDRepGroupAlgebraAdapterReceipt =
  lean-fdrep-group-algebra-adapter-receipt
    "chboishabba/dashi_lean4"
    "agent/monster3b-fdrep-groupalgebra-adapter"
    "Synthesis/MonsterWholeCharacterModuleAdapter.lean"
    "Synthesis/MonsterWholeCharacterModuleAdapterRegression.lean"
    "Synthesis/MonsterWholeCharacterSubmoduleAdapterRegression.lean"
    "Synthesis.fdrep_asModule_action_bridge"
    "Synthesis.fdrep_asModule_submodule_stable"
    "593e23fbce3b254ca024d89c9c8a23baeeabf670"
    "27a37db2c54f46f4a9bfecd196217077f5f50e72"
    "d52cbc8c5b3d0a64b9d8232251248a6ccf6633b6"
    "88886463cacbda416e3c6efb3ea2c6f5eb967e5b"
    "04d4a59bd203cf2987d0818695ea9ed0f070e2cc"
    "408b506d5df99f5c532c4a7446dfeaeefc3624d7"

------------------------------------------------------------------------
-- WrongType / certification firewalls.
------------------------------------------------------------------------

data SourcePresenceCreatesKernelReceipt : Set where
data SameActionAdapterCreatesIsotypicTheorem : Set where
data SubmoduleStabilityCreatesIsotypicTheorem : Set where
data OEISCreatesAdapterTheorem : Set where

sourcePresenceDoesNotCreateKernelReceipt : SourcePresenceCreatesKernelReceipt -> ⊥
sourcePresenceDoesNotCreateKernelReceipt ()

sameActionAdapterDoesNotCreateIsotypicTheorem :
  SameActionAdapterCreatesIsotypicTheorem -> ⊥
sameActionAdapterDoesNotCreateIsotypicTheorem ()

submoduleStabilityDoesNotCreateIsotypicTheorem :
  SubmoduleStabilityCreatesIsotypicTheorem -> ⊥
submoduleStabilityDoesNotCreateIsotypicTheorem ()

oeisDoesNotCreateAdapterTheorem : OEISCreatesAdapterTheorem -> ⊥
oeisDoesNotCreateAdapterTheorem ()

record FDRepGroupAlgebraAdapterBoundary : Set where
  constructor fdrep-group-algebra-adapter-boundary
  field
    leanAdapterSourceWritten : Bool
    sameActionEquationWritten : Bool
    submoduleStabilityAdapterSourceWritten : Bool
    moduleSimpleTypeCanNowReenterRepresentationSide : Bool
    wholeCharacterToIsotypicTheoremWritten : Bool
    leanKernelReceiptObserved : Bool
    agdaTransportObserved : Bool
    oeisCreatesAdapterTheorem : Bool
    nextResidual : String
open FDRepGroupAlgebraAdapterBoundary public

canonicalFDRepGroupAlgebraAdapterBoundary : FDRepGroupAlgebraAdapterBoundary
canonicalFDRepGroupAlgebraAdapterBoundary =
  fdrep-group-algebra-adapter-boundary
    true true true true
    false false false false
    "kernel-check the two exact dashi_lean4 adapters on the pinned v4.28.0 project. The interface debt has now contracted to the representation-theoretic step: use a simple k[G]-submodule of the canonical asModule carrier, transport it back to a G-stable FDRep subspace, then show whole-character multiplicities force every simple type to be H_zeta and the multiplicity to be 90. If that remains expensive, reopen the literal constituent residual. OEIS and dimension identities remain non-promoting."
