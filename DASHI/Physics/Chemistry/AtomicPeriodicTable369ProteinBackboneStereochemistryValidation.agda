module DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinBackboneStereochemistryValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinBackboneStereochemistryExact as P

------------------------------------------------------------------------
-- RED/GREEN validation root for the amino-acid -> peptide-backbone ->
-- conformation cross-pollination.  This file is committed before the owner.
------------------------------------------------------------------------

backboneFibreRegression :
  P.ProteinBackboneStereochemistryBoundary.samePrimarySequenceCanRetainDistinctBackboneResidual
    P.canonicalProteinBackboneStereochemistryBoundary
  ≡ true
  × P.ProteinBackboneStereochemistryBoundary.backboneConformationFactorsThroughPrimarySequenceAlone
    P.canonicalProteinBackboneStereochemistryBoundary
  ≡ false
backboneFibreRegression = refl , refl

sourceRegression :
  P.ProteinBackboneStereochemistryBoundary.ramachandranBackboneConstraintSourcePaid
    P.canonicalProteinBackboneStereochemistryBoundary
  ≡ true
  × P.ProteinBackboneStereochemistryBoundary.pdbArchiveRoutePaid
    P.canonicalProteinBackboneStereochemistryBoundary
  ≡ true
sourceRegression = refl , refl

promotionRegression :
  P.ProteinBackboneStereochemistryBoundary.ramachandranAllowedRegionProvesUniqueFold
    P.canonicalProteinBackboneStereochemistryBoundary
  ≡ false
  × P.ProteinBackboneStereochemistryBoundary.backboneTorsionAloneDeterminesProteinFunction
    P.canonicalProteinBackboneStereochemistryBoundary
  ≡ false
promotionRegression = refl , refl
