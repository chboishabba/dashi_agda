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
-- The current chemistry-right-limits theorem owner.
--
-- This package is stronger than the earlier interpretation/adapter bundle:
-- it contains the concrete quotient-visible 256-slot witness that holds the
-- defect/promoted pair fixed while both the quotient observable and the
-- chemistry-facing cross-band coupling separate.
--
-- It remains pre-spectral and pre-scale-setting.

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
        Contract.chemistryRightLimitsInterpretationContract
    ; rightLimitsAdapter =
        Adapter.atomicChemistryRightLimitsAdapter
    ; observableLaw =
        Observable.chemistryRightLimitsObservableLaw
    ; promotedObservableCoupling =
        Promoted.chemistryRightLimitsPromotedObservableCouplingLaw
    ; quotientObservableCoupling =
        Quotient.chemistryRightLimitsQuotientObservableCouplingLaw
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
        ∷ "The defect/promoted pair is held fixed while quotient and cross-band quantities separate"
        ∷ "No spectrum, energy-scale, bonding, periodic-table, or wet-lab theorem is claimed"
        ∷ []
    }
