module DASHI.Physics.Closure.NSClayFacingCDSourceAuditExact where

------------------------------------------------------------------------
-- CLAY-FACING C/D SOURCE AUDIT
--
-- This file turns the existing source-exact released C/D receipts into a
-- coordinate-by-coordinate audit against Round523's official Fefferman
-- conditions.  No independent reconstruction of ordinary IBP/Gronwall/
-- localization infrastructure is required for this audit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact as Clay
import DASHI.Physics.Closure.NSOpenAI2026ComparatorClayCDSourceExactAlignment as Source

sourcePaysC :
  Clay.ClayBreakdownCoordinate523 → Bool
sourcePaysC Clay.positiveViscosity523 =
  Source.positiveViscosityC Source.releasedClayCSourceReceipt
sourcePaysC Clay.dimensionThree523 =
  Source.dimensionThreeC Source.releasedClayCSourceReceipt
sourcePaysC Clay.smoothDivergenceFreeInitialDatum523 =
  Source.smoothDivergenceFreeDatumC Source.releasedClayCSourceReceipt
sourcePaysC Clay.rapidInitialSpatialDecay523 =
  Source.rapidInitialSpatialDecayC Source.releasedClayCSourceReceipt
sourcePaysC Clay.periodicInitialDatum523 = false
sourcePaysC Clay.smoothForcing523 =
  Source.smoothForcingC Source.releasedClayCSourceReceipt
sourcePaysC Clay.rapidForcingSpaceTimeDecay523 =
  Source.rapidForcingSpaceTimeDecayC Source.releasedClayCSourceReceipt
sourcePaysC Clay.periodicForcing523 = false
sourcePaysC Clay.rapidForcingTimeDecay523 = false
sourcePaysC Clay.exactNavierStokesEquation523 =
  Source.exactEquationC Source.releasedClayCSourceReceipt
sourcePaysC Clay.noGlobalSmoothSolution523 =
  Source.noGlobalSmoothSolutionC Source.releasedClayCSourceReceipt
sourcePaysC Clay.boundedEnergyRequirement523 =
  Source.boundedEnergyConsumerC Source.releasedClayCSourceReceipt
sourcePaysC Clay.periodicSolutionRequirement523 = false

sourcePaysD :
  Clay.ClayBreakdownCoordinate523 → Bool
sourcePaysD Clay.positiveViscosity523 =
  Source.positiveViscosityD Source.releasedClayDSourceReceipt
sourcePaysD Clay.dimensionThree523 =
  Source.dimensionThreeD Source.releasedClayDSourceReceipt
sourcePaysD Clay.smoothDivergenceFreeInitialDatum523 =
  Source.smoothDivergenceFreeDatumD Source.releasedClayDSourceReceipt
sourcePaysD Clay.rapidInitialSpatialDecay523 = false
sourcePaysD Clay.periodicInitialDatum523 =
  Source.periodicInitialDatumD Source.releasedClayDSourceReceipt
sourcePaysD Clay.smoothForcing523 =
  Source.smoothForcingD Source.releasedClayDSourceReceipt
sourcePaysD Clay.rapidForcingSpaceTimeDecay523 = false
sourcePaysD Clay.periodicForcing523 =
  Source.periodicForcingD Source.releasedClayDSourceReceipt
sourcePaysD Clay.rapidForcingTimeDecay523 =
  Source.rapidForcingTimeDecayD Source.releasedClayDSourceReceipt
sourcePaysD Clay.exactNavierStokesEquation523 =
  Source.exactEquationD Source.releasedClayDSourceReceipt
sourcePaysD Clay.noGlobalSmoothSolution523 =
  Source.noGlobalSmoothSolutionD Source.releasedClayDSourceReceipt
sourcePaysD Clay.boundedEnergyRequirement523 = false
sourcePaysD Clay.periodicSolutionRequirement523 =
  Source.periodicSolutionConsumerD Source.releasedClayDSourceReceipt

requiredCIsSourcePaid :
  (coordinate : Clay.ClayBreakdownCoordinate523) →
  Clay.requiredByC523 coordinate ≡ true →
  sourcePaysC coordinate ≡ true
requiredCIsSourcePaid Clay.positiveViscosity523 refl = refl
requiredCIsSourcePaid Clay.dimensionThree523 refl = refl
requiredCIsSourcePaid Clay.smoothDivergenceFreeInitialDatum523 refl = refl
requiredCIsSourcePaid Clay.rapidInitialSpatialDecay523 refl = refl
requiredCIsSourcePaid Clay.periodicInitialDatum523 ()
requiredCIsSourcePaid Clay.smoothForcing523 refl = refl
requiredCIsSourcePaid Clay.rapidForcingSpaceTimeDecay523 refl = refl
requiredCIsSourcePaid Clay.periodicForcing523 ()
requiredCIsSourcePaid Clay.rapidForcingTimeDecay523 ()
requiredCIsSourcePaid Clay.exactNavierStokesEquation523 refl = refl
requiredCIsSourcePaid Clay.noGlobalSmoothSolution523 refl = refl
requiredCIsSourcePaid Clay.boundedEnergyRequirement523 refl = refl
requiredCIsSourcePaid Clay.periodicSolutionRequirement523 ()

requiredDIsSourcePaid :
  (coordinate : Clay.ClayBreakdownCoordinate523) →
  Clay.requiredByD523 coordinate ≡ true →
  sourcePaysD coordinate ≡ true
requiredDIsSourcePaid Clay.positiveViscosity523 refl = refl
requiredDIsSourcePaid Clay.dimensionThree523 refl = refl
requiredDIsSourcePaid Clay.smoothDivergenceFreeInitialDatum523 refl = refl
requiredDIsSourcePaid Clay.rapidInitialSpatialDecay523 ()
requiredDIsSourcePaid Clay.periodicInitialDatum523 refl = refl
requiredDIsSourcePaid Clay.smoothForcing523 refl = refl
requiredDIsSourcePaid Clay.rapidForcingSpaceTimeDecay523 ()
requiredDIsSourcePaid Clay.periodicForcing523 refl = refl
requiredDIsSourcePaid Clay.rapidForcingTimeDecay523 refl = refl
requiredDIsSourcePaid Clay.exactNavierStokesEquation523 refl = refl
requiredDIsSourcePaid Clay.noGlobalSmoothSolution523 refl = refl
requiredDIsSourcePaid Clay.boundedEnergyRequirement523 ()
requiredDIsSourcePaid Clay.periodicSolutionRequirement523 refl = refl

cOfficialCoordinatesSourceAudited : Bool
cOfficialCoordinatesSourceAudited = true

dOfficialCoordinatesSourceAudited : Bool
dOfficialCoordinatesSourceAudited = true

cdIndependentAgdaReconstructionNeededForCoordinateAudit : Bool
cdIndependentAgdaReconstructionNeededForCoordinateAudit = false

cOfficialCoordinatesSourceAuditedIsTrue :
  cOfficialCoordinatesSourceAudited ≡ true
cOfficialCoordinatesSourceAuditedIsTrue = refl

dOfficialCoordinatesSourceAuditedIsTrue :
  dOfficialCoordinatesSourceAudited ≡ true
dOfficialCoordinatesSourceAuditedIsTrue = refl

cdIndependentAgdaReconstructionNeededForCoordinateAuditIsFalse :
  cdIndependentAgdaReconstructionNeededForCoordinateAudit ≡ false
cdIndependentAgdaReconstructionNeededForCoordinateAuditIsFalse = refl
