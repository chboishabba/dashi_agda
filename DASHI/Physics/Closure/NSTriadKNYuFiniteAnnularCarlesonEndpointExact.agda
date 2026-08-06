module DASHI.Physics.Closure.NSTriadKNYuFiniteAnnularCarlesonEndpointExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv:2606.27560v1.
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Prove the finite l1-linfinity endpoint of Yu's Theorem 8.7.  After annular
-- reassignment, each source reservoir A_j sees a half-geometric convolution
-- of core profiles Q_(j+m).  If Q is uniformly bounded and the kernel mass is
-- at most two, then
--
--   sum_j A_j sum_m 2^(-m) Q_(j+m)
--     <= 2 (sum_j A_j) sup_k Q_k.
--
-- This is an actual unconditional finite discrete theorem.  Passing from the
-- PDE far-field term to these rows, controlling the omitted exterior tail,
-- and establishing the source/profile hypotheses remain explicit continuum
-- obligations exactly as in the source paper.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowDyadicGainExact as HalfGeo

record KernelProfileCell : Set where
  constructor kernel-profile-cell
  field
    kernelWeight profileValue : ℚ
    kernelWeightNonnegative : 0ℚ ≤ kernelWeight

open KernelProfileCell public

kernelMass : List KernelProfileCell → ℚ
kernelMass [] = 0ℚ
kernelMass (cell ∷ cells) =
  kernelWeight cell + kernelMass cells

kernelProfilePairing : List KernelProfileCell → ℚ
kernelProfilePairing [] = 0ℚ
kernelProfilePairing (cell ∷ cells) =
  kernelWeight cell * profileValue cell
  + kernelProfilePairing cells

record ReassignedSourceRow : Set where
  constructor reassigned-source-row
  field
    sourceReservoir : ℚ
    profileCells : List KernelProfileCell
    sourceReservoirNonnegative : 0ℚ ≤ sourceReservoir

open ReassignedSourceRow public

sourceMass : List ReassignedSourceRow → ℚ
sourceMass [] = 0ℚ
sourceMass (row ∷ rows) =
  sourceReservoir row + sourceMass rows

reassignedPairing : List ReassignedSourceRow → ℚ
reassignedPairing [] = 0ℚ
reassignedPairing (row ∷ rows) =
  sourceReservoir row * kernelProfilePairing (profileCells row)
  + reassignedPairing rows

record FiniteL1LInfinityCarlesonData : Set₁ where
  constructor finite-l1-linfinity-carleson-data
  field
    rows : List ReassignedSourceRow
    profileSupremum : ℚ
    profileSupremumNonnegative : 0ℚ ≤ profileSupremum

    profileBound :
      (cell : KernelProfileCell) →
      profileValue cell ≤ profileSupremum

    rowKernelMassBound :
      (row : ReassignedSourceRow) →
      kernelMass (profileCells row) ≤ HalfGeo.two

open FiniteL1LInfinityCarlesonData public

kernelProfileBoundByMass :
  (dataSet : FiniteL1LInfinityCarlesonData) →
  (cells : List KernelProfileCell) →
  kernelProfilePairing cells
  ≤ kernelMass cells * profileSupremum dataSet
kernelProfileBoundByMass dataSet [] = ℚₚ.≤-refl
kernelProfileBoundByMass dataSet (cell ∷ cells) =
  let
    cellBound :
      kernelWeight cell * profileValue cell
      ≤ kernelWeight cell * profileSupremum dataSet
    cellBound =
      let
        instance
          kernelIsNonnegative =
            nonNegative (kernelWeightNonnegative cell)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (kernelWeight cell)
        (profileBound dataSet cell)

    summed :
      kernelWeight cell * profileValue cell
        + kernelProfilePairing cells
      ≤ kernelWeight cell * profileSupremum dataSet
        + kernelMass cells * profileSupremum dataSet
    summed =
      ℚₚ.+-mono-≤
        cellBound
        (kernelProfileBoundByMass dataSet cells)

    targetMeaning :
      kernelWeight cell * profileSupremum dataSet
        + kernelMass cells * profileSupremum dataSet
      ≡ (kernelWeight cell + kernelMass cells)
          * profileSupremum dataSet
    targetMeaning =
      solve
        ( kernelWeight cell
        ∷ kernelMass cells
        ∷ profileSupremum dataSet
        ∷ [])
  in
  subst
    (λ upper →
      kernelWeight cell * profileValue cell
        + kernelProfilePairing cells
      ≤ upper)
    targetMeaning
    summed

rowProfileBound :
  (dataSet : FiniteL1LInfinityCarlesonData) →
  (row : ReassignedSourceRow) →
  kernelProfilePairing (profileCells row)
  ≤ HalfGeo.two * profileSupremum dataSet
rowProfileBound dataSet row =
  let
    byMass :
      kernelProfilePairing (profileCells row)
      ≤ kernelMass (profileCells row) * profileSupremum dataSet
    byMass = kernelProfileBoundByMass dataSet (profileCells row)

    scaledKernel :
      kernelMass (profileCells row) * profileSupremum dataSet
      ≤ HalfGeo.two * profileSupremum dataSet
    scaledKernel =
      let
        instance
          profileSupIsNonnegative =
            nonNegative (profileSupremumNonnegative dataSet)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (profileSupremum dataSet)
        (rowKernelMassBound dataSet row)
  in
  ℚₚ.≤-trans byMass scaledKernel

finiteAnnularCarlesonEndpoint :
  (dataSet : FiniteL1LInfinityCarlesonData) →
  reassignedPairing (rows dataSet)
  ≤ HalfGeo.two * sourceMass (rows dataSet)
      * profileSupremum dataSet
finiteAnnularCarlesonEndpoint dataSet = go (rows dataSet)
  where
  go :
    (remaining : List ReassignedSourceRow) →
    reassignedPairing remaining
    ≤ HalfGeo.two * sourceMass remaining
        * profileSupremum dataSet
  go [] = ℚₚ.≤-refl
  go (row ∷ remaining) =
    let
      scaledRow :
        sourceReservoir row * kernelProfilePairing (profileCells row)
        ≤ sourceReservoir row
            * (HalfGeo.two * profileSupremum dataSet)
      scaledRow =
        let
          instance
            sourceIsNonnegative =
              nonNegative (sourceReservoirNonnegative row)
        in
        ℚₚ.*-monoˡ-≤-nonNeg
          (sourceReservoir row)
          (rowProfileBound dataSet row)

      summed :
        sourceReservoir row * kernelProfilePairing (profileCells row)
          + reassignedPairing remaining
        ≤ sourceReservoir row
            * (HalfGeo.two * profileSupremum dataSet)
          + HalfGeo.two * sourceMass remaining
            * profileSupremum dataSet
      summed = ℚₚ.+-mono-≤ scaledRow (go remaining)

      targetMeaning :
        sourceReservoir row
            * (HalfGeo.two * profileSupremum dataSet)
          + HalfGeo.two * sourceMass remaining
            * profileSupremum dataSet
        ≡ HalfGeo.two
            * (sourceReservoir row + sourceMass remaining)
            * profileSupremum dataSet
      targetMeaning =
        solve
          ( sourceReservoir row
          ∷ sourceMass remaining
          ∷ profileSupremum dataSet
          ∷ [])
    in
    subst
      (λ upper →
        sourceReservoir row * kernelProfilePairing (profileCells row)
          + reassignedPairing remaining
        ≤ upper)
      targetMeaning
      summed
