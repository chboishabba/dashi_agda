module DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationIntegration where

------------------------------------------------------------------------
-- Authoritative receipt for the official Luo identification tranche.
--
-- Machine-checked construction surfaces:
--   * selected coefficient-unitary official finite Hermitian pairing;
--   * hard-projector orthogonality for that selected pairing;
--   * exact physical-triad -> concrete Z3 resonant-pair encoding;
--   * rational full-shell -> physical bridge constructor;
--   * four definitional cross-carrier equalities;
--   * typed regular Leray--Hopf carrier with factor-two dissipation;
--   * separation of weak energy inequality and pre-terminal energy identity;
--   * official energy/dissipation/pointwise-flux/integrated-flux/window owner;
--   * final official continuation composition.
--
-- Standard-imported selections:
--   * smooth normalized-exponential radial multiplier and periodized kernel L1
--     theorem;
--   * Luo Theorem 1.1 on T3 at unit viscosity.
--
-- No standard-imported theorem self-promotes the BKM/Clay gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNOfficialFiniteFourierHermitianParsevalExact as Parseval
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNHardHighPhysicalZ3PairEncodingExact as Encoding
import DASHI.Physics.Closure.NSTriadKNLuoCrossCarrierRationalIdentificationExact as Cross
import DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact as LH
import DASHI.Physics.Closure.NSTriadKNLuoOfficialPhysicalEnergyTimeExact as EnergyTime
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Authority
import DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationClosureExact as Closure
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileBounds as PairBounds

record OfficialLuoContinuationIntegrationReceipt : Set where
  constructor receipt
  field
    officialFiniteFourierPairingSelected :
      Parseval.officialFiniteFourierPairingSelected ≡ true

    officialHardProjectorOrthogonalConstructed :
      Parseval.officialPhysicalHardProjectorOrthogonalConstructed ≡ true

    concreteRadialCutoffSelected :
      Multiplier.canonicalLuoRadialCutoffSelected ≡ true

    cutoffUniformKernelL1BoundSelected :
      Multiplier.cutoffUniformPeriodicKernelL1BoundSelected ≡ true

    hardHighPhysicalZ3EncodingClosed :
      Encoding.hardHighPhysicalToZ3PairEncodingClosed ≡ true

    hardHighResonanceTransportClosed :
      Encoding.hardHighPhysicalResonanceTransportClosed ≡ true

    fourCrossCarrierEqualitiesClosed :
      Cross.fourCrossCarrierEqualitiesClosed ≡ true

    physicalWeightedSchurBridgeConstructorClosed :
      Cross.physicalWeightedSchurBridgeConstructorClosed ≡ true

    regularLerayHopfCarrierConstructed :
      LH.regularLerayHopfCarrierConstructed ≡ true

    factorTwoDissipationRecorded :
      LH.factorTwoDissipationNormalizationRecorded ≡ true

    weakInequalityAndRegularIdentitySeparated :
      LH.preterminalEnergyIdentitySeparatedFromWeakInequality ≡ true

    officialEnergyTimeCarrierSelected :
      EnergyTime.officialPhysicalEnergyTimeCarrierSelected ≡ true

    energyDissipationIdentitiesClosed :
      EnergyTime.officialEnergyDissipationIdentitiesClosed ≡ true

    pointwiseIntegratedFluxClosed :
      EnergyTime.officialPointwiseIntegratedFluxIdentificationClosed ≡ true

    terminalWindowIdentificationClosed :
      EnergyTime.officialTerminalWindowIdentificationClosed ≡ true

    officialLuoCarrierSelected :
      Authority.officialPeriodicLuoCarrierSelected ≡ true

    unitViscosityThreeTorusSelected :
      Authority.unitViscosityThreeTorusIdentificationSelected ≡ true

    regularLerayHopfSourceSelected :
      Authority.regularLerayHopfSourceIdentificationSelected ≡ true

    officialContinuationClosureConstructed :
      Closure.officialLuoContinuationClosureConstructed ≡ true

    allSixTasksComposed :
      Closure.allSixOfficialIdentificationTasksComposed ≡ true

    BKMExclusionStillFalse :
      PairBounds.canonicalBKMExclusionProved ≡ false

    ClayPromotionStillFalse :
      PairBounds.clayPromoted
        PairBounds.canonicalNSTriadKNPairIncidenceProfileBounds
        ≡ false

open OfficialLuoContinuationIntegrationReceipt public

officialLuoContinuationIntegrationReceipt :
  OfficialLuoContinuationIntegrationReceipt
officialLuoContinuationIntegrationReceipt = receipt
  Parseval.officialFiniteFourierPairingSelectedIsTrue
  Parseval.officialPhysicalHardProjectorOrthogonalConstructedIsTrue
  Multiplier.canonicalLuoRadialCutoffSelectedIsTrue
  Multiplier.cutoffUniformPeriodicKernelL1BoundSelectedIsTrue
  Encoding.hardHighPhysicalToZ3PairEncodingClosedIsTrue
  Encoding.hardHighPhysicalResonanceTransportClosedIsTrue
  Cross.fourCrossCarrierEqualitiesClosedIsTrue
  Cross.physicalWeightedSchurBridgeConstructorClosedIsTrue
  LH.regularLerayHopfCarrierConstructedIsTrue
  LH.factorTwoDissipationNormalizationRecordedIsTrue
  LH.preterminalEnergyIdentitySeparatedFromWeakInequalityIsTrue
  EnergyTime.officialPhysicalEnergyTimeCarrierSelectedIsTrue
  EnergyTime.officialEnergyDissipationIdentitiesClosedIsTrue
  EnergyTime.officialPointwiseIntegratedFluxIdentificationClosedIsTrue
  EnergyTime.officialTerminalWindowIdentificationClosedIsTrue
  Authority.officialPeriodicLuoCarrierSelectedIsTrue
  Authority.unitViscosityThreeTorusIdentificationSelectedIsTrue
  Authority.regularLerayHopfSourceIdentificationSelectedIsTrue
  Closure.officialLuoContinuationClosureConstructedIsTrue
  Closure.allSixOfficialIdentificationTasksComposedIsTrue
  refl
  (PairBounds.clayPromotedIsFalse
    PairBounds.canonicalNSTriadKNPairIncidenceProfileBounds)

officialLuoIdentificationTrancheComplete : Bool
officialLuoIdentificationTrancheComplete = true

officialLuoRouteReadyForClayPromotion : Bool
officialLuoRouteReadyForClayPromotion = false

officialLuoIdentificationTrancheCompleteIsTrue :
  officialLuoIdentificationTrancheComplete ≡ true
officialLuoIdentificationTrancheCompleteIsTrue = refl

officialLuoRouteReadyForClayPromotionIsFalse :
  officialLuoRouteReadyForClayPromotion ≡ false
officialLuoRouteReadyForClayPromotionIsFalse = refl
