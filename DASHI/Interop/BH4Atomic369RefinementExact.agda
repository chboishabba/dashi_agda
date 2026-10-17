module DASHI.Interop.BH4Atomic369RefinementExact where

open import DASHI.Core.Prelude

import DASHI.Biology.Molecular.BH4MolecularStoichiometryExact as Stoich
import DASHI.Biology.NonginNangNitrogenOxideRefinementExact as NongNang
import DASHI.Core.ArgumentLevelTransportHyperformalismExact as ArgumentLevelTransportHyperformalismExact
import DASHI.Interop.PNFHyperfabric369 as H369
import DASHI.Physics.Foundations.AtomicGenerationPipelineExact as AtomicGenerationPipelineExact
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- BH4 / atomics / 369 refinement adapter.
--
-- The shared shape is level-indexed observation with retained residuals. The
-- chemistry is not identified with the 3/6/9 address geometry. Instead the
-- 369 carrier supplies an already-existing refinement vocabulary for keeping a
-- whole object while moving between coarse and fine observations.
------------------------------------------------------------------------

data BH4InspectionLevel : Set where
  atomicInventoryLevel : BH4InspectionLevel
  molecularReactionLevel : BH4InspectionLevel
  biochemicalProjectionLevel : BH4InspectionLevel
  compartmentFluxLevel : BH4InspectionLevel

data BH4Projection : Set where
  atomInventoryProjection : BH4Projection
  reactionIdentityProjection : BH4Projection
  bh4AvailabilityProjection : BH4Projection
  nitrogenOxideProjection : BH4Projection
  fineCompartmentRedoxProjection : BH4Projection

record BH4RefinementCarrier : Set where
  constructor bh4-refinement-carrier
  field
    wholeReference : String
    currentLevel : BH4InspectionLevel
    projection : BH4Projection
    retainedProvenance : String
    residualReference : String

open BH4RefinementCarrier public

qdprAtomicInventoryView : BH4RefinementCarrier
qdprAtomicInventoryView = bh4-refinement-carrier
  "RHEA:32253 / QDPR BH4-regeneration reaction"
  atomicInventoryLevel atomInventoryProjection
  "Rhea/ChEBI exact participants + DASHI molecular stoichiometry receipt"
  "electronic structure and molecular Hamiltonian remain external/open"

qdprReactionView : BH4RefinementCarrier
qdprReactionView = bh4-refinement-carrier
  "RHEA:32253 / QDPR BH4-regeneration reaction"
  molecularReactionLevel reactionIdentityProjection
  "same Rhea/ChEBI provenance retained"
  "reaction identity does not supply kinetics or compartment state"

qdprCoarseBH4View : BH4RefinementCarrier
qdprCoarseBH4View = bh4-refinement-carrier
  "BH4 system state containing the QDPR reaction"
  biochemicalProjectionLevel bh4AvailabilityProjection
  "same biochemical carrier; coarse atlas projection only"
  "BH4/BH2 amounts, redox ratio, compartment, occupancy and flux are forgotten"

atomicGenerationBoundary : AtomicGenerationPipelineExact.AtomicGenerationBoundary
atomicGenerationBoundary = AtomicGenerationPipelineExact.canonicalAtomicGenerationBoundary

nonaryDimensionAvailable : H369.nonaryDimension ≡ 9
nonaryDimensionAvailable = refl

qdprFiniteStoichiometryAvailable : Stoich.qdprAtomAndChargeBalanced ≡ true
qdprFiniteStoichiometryAvailable = refl

-- Literal theorem reuse from the existing NONG/NANG refinement lane.  A
-- coarse nitrogen-oxide observation cannot satisfy the consumer that requires
-- the fine NO-versus-N2O chemical frame.
coarseNitrogenOxideCannotServeFineChemicalConsumer :
  NongNang.CoarseChemicalDescent → ⊥
coarseNitrogenOxideCannotServeFineChemicalConsumer =
  NongNang.coarseNitrogenOxideCannotServeFineConsumer

record BH4Atomic369Boundary : Set where
  constructor bh4-atomic-369-boundary
  field
    atomicInventorySolvesMolecularHamiltonian : Bool
    atomicInventorySolvesMolecularHamiltonianIsFalse : atomicInventorySolvesMolecularHamiltonian ≡ false
    finiteStoichiometryPredictsQuantitativeChemistry : Bool
    finiteStoichiometryPredictsQuantitativeChemistryIsFalse : finiteStoichiometryPredictsQuantitativeChemistry ≡ false
    coarseBH4AvailabilityReconstructsFineChemicalState : Bool
    coarseBH4AvailabilityReconstructsFineChemicalStateIsFalse : coarseBH4AvailabilityReconstructsFineChemicalState ≡ false
    coarseNitrogenOxideReconstructsNOvsN2OState : Bool
    coarseNitrogenOxideReconstructsNOvsN2OStateIsFalse : coarseNitrogenOxideReconstructsNOvsN2OState ≡ false
    chemistryIsLiterally369 : Bool
    chemistryIsLiterally369IsFalse : chemistryIsLiterally369 ≡ false
    commonRefinementShapeIdentifiesSemantics : Bool
    commonRefinementShapeIdentifiesSemanticsIsFalse : commonRefinementShapeIdentifiesSemantics ≡ false

open BH4Atomic369Boundary public

canonicalBH4Atomic369Boundary : BH4Atomic369Boundary
canonicalBH4Atomic369Boundary =
  bh4-atomic-369-boundary
    false refl false refl false refl false refl false refl false refl

canonicalBH4Atomic369Receipt : Receipt.GenericReceipt
canonicalBH4Atomic369Receipt =
  Receipt.mkNonPromotingReceipt
    "BH4 atomics / 369 refinement adapter"
    "DASHI.Interop.BH4Atomic369RefinementExact"
    "QDPR atom inventory -> molecular reaction -> coarse BH4 projection -> fine compartment/redox residual; literal reuse of Nongin NO/N2O non-descent"
    "reuses AtomicGenerationPipelineExact and the argument-level/369 refinement grammar while retaining the whole biochemical reference and provenance"
    "atomic inventory is not a solved molecular Hamiltonian; finite balance is not quantitative chemistry; coarse projection does not reconstruct fine state; chemistry is not literally 369"
    "agda -i . DASHI/Interop/BH4Atomic369RefinementExact.agda"
