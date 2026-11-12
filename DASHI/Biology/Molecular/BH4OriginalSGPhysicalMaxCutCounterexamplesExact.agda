module DASHI.Biology.Molecular.BH4OriginalSGPhysicalMaxCutCounterexamplesExact where

-- Kernel-checkable finite counterexample to the false P0 claim
-- that a closed SG system preserves EACH CELL's conserved mass.
--
-- The existing finite electrodiffusive two-volume transfer
-- already witnesses local redistribution with global conservation.
-- It is a structural counterexample, not the original Rhea kinetics.
-- Global six-axis sums can be constant while individual voxel
-- source-weighted totals change due to face flux divergence.

open import DASHI.Core.Prelude
import DASHI.Biology.Physical.FiniteElectrodiffusiveMovingBoundaryExact as ED

initialState : ED.IonPairState
initialState = ED.ionPair 3 1

afterOneNativeTransfer : ED.IonPairState
afterOneNativeTransfer = ED.transport ED.leftToRight initialState

initialCellOneAmount : ED.left initialState ≡ 3
initialCellOneAmount = refl

afterCellOneAmount : ED.left afterOneNativeTransfer ≡ 2
afterCellOneAmount = refl

localMassActuallyChanges :
  ED.left afterOneNativeTransfer ≡ ED.left initialState → ⊥
localMassActuallyChanges ()

totalNativeMassConserved :
  ED.totalAmount afterOneNativeTransfer ≡ ED.totalAmount initialState
totalNativeMassConserved =
  ED.transportConservesAmount ED.leftToRight initialState

originalGlobalNotCellwiseCounterexample :
  (ED.totalAmount afterOneNativeTransfer
    ≡ ED.totalAmount initialState)
  × (ED.left afterOneNativeTransfer
    ≡ ED.left initialState → ⊥)
originalGlobalNotCellwiseCounterexample =
  totalNativeMassConserved , localMassActuallyChanges

-- Correct physical invariant is globally volume-weighted mass
-- (with one closed-domain total per conserved source weight),
-- NOT a product of per-voxel fixed-mass simplices.
-- The actual Poisson/SG and original Rhea source still require
-- further exact physical identification and Agda acceptance.
