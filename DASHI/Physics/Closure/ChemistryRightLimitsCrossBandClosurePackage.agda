module DASHI.Physics.Closure.ChemistryRightLimitsCrossBandClosurePackage where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryRightLimitsInterpretationContract as Contract
import DASHI.Physics.Closure.AtomicChemistryRightLimitsAdapter as Adapter
import DASHI.Physics.Closure.ChemistryRightLimitsObservableLaw as Observable
import DASHI.Physics.Closure.ChemistryRightLimitsPromotedObservableCouplingLaw as Promoted
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientObservableCouplingLaw as Quotient
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness as Witness

------------------------------------------------------------------------
-- Current chemistry-right-limits theorem owner.
--
-- The earlier interpretation contract, adapter, first observable, promoted
-- pair, and quotient observable are consumed here by the concrete 256-slot
-- cross-band witness.  The witness holds the defect/promoted pair fixed while
-- both the quotient observable and a chemistry-facing cross-band quantity
-- separate.  This is the non-vacuous pre-spectral law requested by the board.
--
-- Spectra, scale setting, bonding, and empirical chemistry remain outside the
-- theorem.

record ChemistryRightLimitsCrossBandClosurePackage : Setω where
  field
    interpretationContract :
      Contract.ChemistryRightLimitsInterpretationContract

    rightLimitsAdapter :
      Adapter.AtomicChemistryRightLimitsAdapter

    observableLaw :
      Observable.ChemistryRightLimitsObservableLaw

    promotedObservableCoupling :
      Promoted.ChemistryRightLimitsPromotedObservableCouplingLaw

    quotientObservableCoupling :
      Quotient.ChemistryRightLimitsQuotientObservableCouplingLaw

    concreteCrossBandRequirement :
      CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement

    concreteCrossBandTheorem :
      CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingTheorem

    concreteChemistryLaw :
      CrossBand.ChemistryRightLimitsLaw concreteCrossBandRequirement

    concreteQuotientCrossBandLaw :
      CrossBand.ChemistryRightLimitsQuotientCrossBandLaw

    claimBoundary : List String

canonicalChemistryRightLimitsCrossBandClosurePackage :
  ChemistryRightLimitsCrossBandClosurePackage
canonicalChemistryRightLimitsCrossBandClosurePackage =
  record
    { interpretationContract =
        Contract.canonicalChemistryRightLimitsInterpretationContract
    ; rightLimitsAdapter =
        Adapter.canonicalAtomicChemistryRightLimitsAdapter
    ; observableLaw =
        Observable.canonicalChemistryRightLimitsObservableLaw
    ; promotedObservableCoupling =
        Promoted.canonicalChemistryRightLimitsPromotedObservableCouplingLaw
    ; quotientObservableCoupling =
        Quotient.canonicalChemistryRightLimitsQuotientObservableCouplingLaw
    ; concreteCrossBandRequirement =
        Witness.canonicalQuotientCrossBandCouplingRequirementWitness
    ; concreteCrossBandTheorem =
        Witness.canonicalQuotientCrossBandCouplingTheoremWitness
    ; concreteChemistryLaw =
        Witness.canonicalCandidate256ChemistryRightLimitsLaw
    ; concreteQuotientCrossBandLaw =
        Witness.canonicalCandidate256QuotientCrossBandLaw
    ; claimBoundary =
        "The quotient-visible chemistry blocker is discharged on the concrete 256-slot witness"
        ∷ "The defect/promoted pair is fixed while quotient and cross-band quantities separate"
        ∷ "The theorem remains pre-spectral and pre-scale-setting"
        ∷ "No bonding, periodic-table, wet-lab, or empirical-validation theorem is claimed"
        ∷ []
    }
