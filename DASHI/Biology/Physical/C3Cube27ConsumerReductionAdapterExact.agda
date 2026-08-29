module DASHI.Biology.Physical.C3Cube27ConsumerReductionAdapterExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Biology.Physical.C3CubeFourier27Exact as C3

------------------------------------------------------------------------
-- REPOSITORY-NATIVE ADAPTER
--
-- The imported C3CubeFourier27Exact owner establishes the exact finite C3^3
-- / 27-cell carrier.  This module asks a deliberately narrower question:
-- can that genuine symmetry act compatibly with the generic consumer-relative
-- reduction kernel?  Yes, for the identity reduction below.
--
-- Nothing here claims that 3, 6, 9 or 27 is a universal natural code, that a
-- 27-state application ought to possess C3^3 symmetry, or that cardinality
-- alone supplies dynamics.  Applications must provide their own symmetry
-- action and equivariance witness if symmetry is relevant at all.
------------------------------------------------------------------------

Cell : Set
Cell = C3.CubeCell27

Shift : Set
Shift = C3.Cube3

translate : Shift → Cell → Cell
translate shift cell =
  C3.cubeToCell (C3.cubeAdd shift (C3.cellToCube cell))

identity27Reduction : Reduction.ConsumerRelativeReduction Cell Shift Cell
identity27Reduction = Reduction.consumerRelativeReduction
  Cell
  (λ cell → cell)
  translate
  translate
  (λ cell → cell)
  (λ cell → cell)
  (λ shift cell → refl)
  (λ cell → refl)

fineC3CubeSymmetry : Reduction.SymmetryAction Cell
fineC3CubeSymmetry = Reduction.symmetryAction Shift translate

reducedC3CubeSymmetry : Reduction.SymmetryAction (Reduction.Reduced identity27Reduction)
reducedC3CubeSymmetry = Reduction.symmetryAction Shift translate

identity27SymmetryCompatible :
  Reduction.SymmetryCompatibleReduction
    identity27Reduction fineC3CubeSymmetry reducedC3CubeSymmetry
identity27SymmetryCompatible = Reduction.symmetryCompatibleReduction
  (λ shift → shift)
  (λ shift cell → refl)

identity27FuturePreserved :
  (shifts : List Shift) →
  (cell : Cell) →
  Reduction.fineObserve identity27Reduction
    (Reduction.run (Reduction.fineStep identity27Reduction) shifts cell)
  ≡ Reduction.reducedObserve identity27Reduction
    (Reduction.run (Reduction.reducedStep identity27Reduction) shifts
      (Reduction.encode identity27Reduction cell))
identity27FuturePreserved = Reduction.consumerFuturePreserved identity27Reduction

record C3Cube27ReductionBoundary : Set where
  constructor c3Cube27ReductionBoundary
  field
    exactC3Cube27StructureExists : Bool
    exactC3Cube27StructureExistsIsTrue : exactC3Cube27StructureExists ≡ true

    everyConsumerReductionRequiresSymmetry : Bool
    everyConsumerReductionRequiresSymmetryIsFalse :
      everyConsumerReductionRequiresSymmetry ≡ false

    cardinality27ImpliesC3CubeMechanism : Bool
    cardinality27ImpliesC3CubeMechanismIsFalse :
      cardinality27ImpliesC3CubeMechanism ≡ false

    numbers369DeterminePhysicalOntology : Bool
    numbers369DeterminePhysicalOntologyIsFalse :
      numbers369DeterminePhysicalOntology ≡ false

    genuineApplicationSymmetryMayBeUsedWhenWitnessed : Bool
    genuineApplicationSymmetryMayBeUsedWhenWitnessedIsTrue :
      genuineApplicationSymmetryMayBeUsedWhenWitnessed ≡ true

open C3Cube27ReductionBoundary public

canonicalC3Cube27ReductionBoundary : C3Cube27ReductionBoundary
canonicalC3Cube27ReductionBoundary =
  c3Cube27ReductionBoundary true refl false refl false refl false refl true refl
