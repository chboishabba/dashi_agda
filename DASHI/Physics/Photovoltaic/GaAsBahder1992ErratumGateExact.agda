module DASHI.Physics.Photovoltaic.GaAsBahder1992ErratumGateExact where

-- Bahder primary-source correction ledger: SOURCE-WRITTEN, not
-- Agda Golden kernel accepted. P1d original PRB 41 11992 (1990);
-- erratum PRB 46 9913 (1992), one page, verified against source PDF.
-- Reuse the existing GaAs optical/Bir-Pikus owner. No 8x8 matrix identity
-- is asserted from DOIs or imported symbolic Python source alone.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Photovoltaic.GaAs111BirPikusC3vFiniteExact as BP
import DASHI.Physics.Photovoltaic.GaAs111OpticalDeviceSourceWeldExact as Optical

data ErratumObligation : Set where
  Corrected1992SpinOrbitN1N2N3 : ErratumObligation
  Corrected1992ValenceHydrostaticA : ErratumObligation
  Corrected1992ValenceMixingR : ErratumObligation
  Corrected1992PQRSPlanckSquare : ErratumObligation
  Original1990InterbandKStrain : ErratumObligation
  SameGammaEightSixBasis : ErratumObligation
  SourcePaidDeviceStrain : ErratumObligation

-- Existing exact/abstract or symbolic status of THIS REPO BRANCH;
-- numeric symbolic script checks 1992 N1/N2/N3 matrix formula but
-- has not been welded to original 8band Hamiltonian in the SAME basis.
erratumImplementedInSource : ErratumObligation -> Bool
erratumImplementedInSource Corrected1992SpinOrbitN1N2N3 = true
erratumImplementedInSource Corrected1992ValenceHydrostaticA = false
erratumImplementedInSource Corrected1992ValenceMixingR = false
erratumImplementedInSource Corrected1992PQRSPlanckSquare = false
erratumImplementedInSource Original1990InterbandKStrain = false
erratumImplementedInSource SameGammaEightSixBasis = false
erratumImplementedInSource SourcePaidDeviceStrain = false

spinOrbitAlgebraSourceWritten :
  erratumImplementedInSource Corrected1992SpinOrbitN1N2N3 ≡ true
spinOrbitAlgebraSourceWritten = refl

data False : Set where

erratumRCorrectionCannotBeAssumed :
  erratumImplementedInSource Corrected1992ValenceMixingR ≡ true -> False
erratumRCorrectionCannotBeAssumed ()

fullBahderCannotBeClaimedFromCurrentStatus :
  erratumImplementedInSource SameGammaEightSixBasis ≡ true -> False
fullBahderCannotBeClaimedFromCurrentStatus ()

-- Each witness is defined as a *dependent, source-specific proof carrier*.
-- It must be inhabited by a real common-basis Hamiltonian/eigenpair proof;
-- no trivially inhabited synthetic receipt is supplied in this module.
record FullBahder1992SameMaterialAcceptance : Set₁ where
  field
    SameEightStateBasis : Set
    actualSameEightStateBasis : SameEightStateBasis
    CorrectedSOOperator : Set
    correctedSOOperator : CorrectedSOOperator
    CorrectedValenceR : Set
    correctedValenceR : CorrectedValenceR
    CorrectedHydrostaticConvention : Set
    correctedHydrostaticConvention : CorrectedHydrostaticConvention
    CorrectedPlanckDimensions : Set
    correctedPlanckDimensions : CorrectedPlanckDimensions
    RealInterbandStrainK : Set
    realInterbandStrainK : RealInterbandStrainK
    SameMaterialOpticalExperiment : Set
    sameMaterialOpticalExperiment : SameMaterialOpticalExperiment

-- The physical acceptance remains UNINHABITED.
