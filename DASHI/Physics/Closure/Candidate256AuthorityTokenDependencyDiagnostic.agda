module DASHI.Physics.Closure.Candidate256AuthorityTokenDependencyDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BlockerKillConditions as Kill
import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness as Candidate256
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Candidate256 authority-token dependency diagnostic.
--
-- This module is non-promoting.  It records the exact dependency path from
-- the landed Candidate256 TSFV-style quotient/cross-band law to the W4 kill
-- condition and names the constructorless boundary.  It does not construct a
-- Candidate256PhysicalCalibrationAuthorityToken, an external calibration
-- receipt, a W4 kill authority, or W4 promotion.

data Candidate256AuthorityDependencyBoundary : Set where
  landedCandidate256TSFVStyleLaw :
    Candidate256AuthorityDependencyBoundary
  dimensionlessSurrogateScaleOnly :
    Candidate256AuthorityDependencyBoundary
  constructorlessPhysicalCalibrationAuthorityToken :
    Candidate256AuthorityDependencyBoundary
  externalReceiptBlockedByAuthorityToken :
    Candidate256AuthorityDependencyBoundary
  w4KillBlockedByExternalReceipt :
    Candidate256AuthorityDependencyBoundary

canonicalCandidate256AuthorityDependencyBoundaries :
  List Candidate256AuthorityDependencyBoundary
canonicalCandidate256AuthorityDependencyBoundaries =
  landedCandidate256TSFVStyleLaw
  ∷ dimensionlessSurrogateScaleOnly
  ∷ constructorlessPhysicalCalibrationAuthorityToken
  ∷ externalReceiptBlockedByAuthorityToken
  ∷ w4KillBlockedByExternalReceipt
  ∷ []

w4KillAuthorityImpossibleHere :
  (receipt : External.Candidate256PhysicalCalibrationExternalReceipt) →
  Kill.W4KillAuthority receipt →
  ⊥
w4KillAuthorityImpossibleHere receipt authority =
  External.candidate256PhysicalCalibrationAuthorityTokenImpossibleHere
    (Kill.W4KillAuthority.calibrationAuthority authority)

w4KillReceiptImpossibleHere :
  External.Candidate256PhysicalCalibrationExternalReceipt →
  ⊥
w4KillReceiptImpossibleHere =
  External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere

record Candidate256AuthorityTokenDependencyDiagnostic : Setω where
  field
    candidate256TSFVStyleLaw :
      CrossBand.ChemistryRightLimitsQuotientCrossBandLaw

    candidate256TSFVStyleLawName :
      String

    strictPhysicalLawAliasName :
      String

    tsfvKernel :
      CrossBand.TimeSymmetricCrossBandKernel

    handoffPreReceipt :
      Handoff.ChemistryPhysicalHandoffPreReceipt

    surrogateBoundary :
      Surrogate.Candidate256SurrogateScaleSettingBoundaryReceipt

    gateStatus :
      Gate.Candidate256PhysicalCalibrationCurrentStatus

    externalReceiptStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    w4KillCondition :
      Kill.KillCondition

    w4KillCurrentlyBlocked :
      Kill.KillCondition.currentState w4KillCondition
      ≡
      Kill.blocked

    minimalDependencyMap :
      List String

    exactAuthorityTokenTypeName :
      String

    exactExternalReceiptTypeName :
      String

    exactW4KillAuthorityTypeName :
      String

    exactW4KillEvidenceTypeName :
      String

    exactConstructorlessBoundary :
      String

    dependencyBoundaries :
      List Candidate256AuthorityDependencyBoundary

    noPromotionBoundary :
      List String

    authorityTokenImpossibleHere :
      Gate.Candidate256PhysicalCalibrationAuthorityToken →
      ⊥

    externalReceiptImpossibleHere :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    w4KillAuthorityImpossible :
      (receipt : External.Candidate256PhysicalCalibrationExternalReceipt) →
      Kill.W4KillAuthority receipt →
      ⊥

canonicalCandidate256AuthorityTokenDependencyDiagnostic :
  Candidate256AuthorityTokenDependencyDiagnostic
canonicalCandidate256AuthorityTokenDependencyDiagnostic =
  record
    { candidate256TSFVStyleLaw =
        Candidate256.canonicalCandidate256QuotientCrossBandLaw
    ; candidate256TSFVStyleLawName =
        "Candidate256.canonicalCandidate256QuotientCrossBandLaw"
    ; strictPhysicalLawAliasName =
        "Next.canonicalCandidate256QuotientLaw"
    ; tsfvKernel =
        CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.timeSymmetricKernel
          Candidate256.canonicalCandidate256QuotientCrossBandLaw
    ; handoffPreReceipt =
        Handoff.canonicalChemistryPhysicalHandoffPreReceipt
    ; surrogateBoundary =
        Surrogate.canonicalCandidate256SurrogateScaleSettingBoundaryReceipt
    ; gateStatus =
        Gate.canonicalCandidate256PhysicalCalibrationCurrentStatus
    ; externalReceiptStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; w4KillCondition =
        Kill.w4KillCondition
    ; w4KillCurrentlyBlocked =
        refl
    ; minimalDependencyMap =
        "Candidate256.canonicalCandidate256QuotientCrossBandLaw: landed TSFV-style quotient/cross-band law"
        ∷ "Surrogate.candidate256SurrogateScale: Nat-valued dimensionless quotient-class scale"
        ∷ "Gate.Candidate256PhysicalCalibrationAuthorityToken: constructorless authority token required by physical calibration"
        ∷ "External.Candidate256PhysicalCalibrationExternalReceipt.calibrationAuthority: exact receipt field carrying that token"
        ∷ "External.Candidate256PhysicalCalibrationExternalReceipt.physicalUnitCarrier: exact W4 kill evidence field target"
        ∷ "Kill.W4KillAuthority: requires token matching External.Candidate256PhysicalCalibrationExternalReceipt.calibrationAuthority"
        ∷ "Kill.W4KillEvidence: requires physicalUnitCarrier matching External.Candidate256PhysicalCalibrationExternalReceipt.physicalUnitCarrier"
        ∷ "Kill.w4KillCondition.currentState: blocked"
        ∷ []
    ; exactAuthorityTokenTypeName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationGate.Candidate256PhysicalCalibrationAuthorityToken"
    ; exactExternalReceiptTypeName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt"
    ; exactW4KillAuthorityTypeName =
        "DASHI.Physics.Closure.BlockerKillConditions.W4KillAuthority"
    ; exactW4KillEvidenceTypeName =
        "DASHI.Physics.Closure.BlockerKillConditions.W4KillEvidence"
    ; exactConstructorlessBoundary =
        "Candidate256PhysicalCalibrationAuthorityToken has no constructors; External.candidate256PhysicalCalibrationAuthorityTokenImpossibleHere eliminates any local token"
    ; dependencyBoundaries =
        canonicalCandidate256AuthorityDependencyBoundaries
    ; noPromotionBoundary =
        "No Candidate256PhysicalCalibrationAuthorityToken is constructed here"
        ∷ "No Candidate256PhysicalCalibrationExternalReceipt is constructed here"
        ∷ "No W4KillAuthority or W4KillEvidence is constructed here"
        ∷ "The landed TSFV-style Candidate256 law remains pre-physical and dimensionless until external calibration authority supplies units, calibration, factorization, and dimensional preservation"
        ∷ "No W4 kill, chemistry promotion, matter/stress-energy handoff, or unification claim is made here"
        ∷ []
    ; authorityTokenImpossibleHere =
        External.candidate256PhysicalCalibrationAuthorityTokenImpossibleHere
    ; externalReceiptImpossibleHere =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    ; w4KillAuthorityImpossible =
        w4KillAuthorityImpossibleHere
    }
