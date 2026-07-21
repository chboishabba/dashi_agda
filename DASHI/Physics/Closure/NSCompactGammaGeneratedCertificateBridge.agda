module DASHI.Physics.Closure.NSCompactGammaGeneratedCertificateBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact consumer surface for the Python-generated certificate bundle.
--
-- The finite certificate is useful only after its deterministic checker has
-- accepted the exact rational core.  It cannot inhabit an infinite periodic
-- Fourier theorem by itself.  The analytic tail obligations are therefore
-- explicit fields and the bridge merely assembles them without promotion.
------------------------------------------------------------------------

record ExactFiniteCertificateCore (i : Level) : Set (lsuc i) where
  field
    Certificate : Set i
    acceptedCertificate : Certificate

    schemaName certificateDigest : String
    finiteCoreExhaustive : Set i

    adjacentUnconditionalContractionRefuted : Set i
    nearTriadOddnessExact : Set i
    nearSignedCoercivityRefuted : Set i
    nearFiniteCoreAbsorptionVerified : Set i
    radiusEightFarLowCoreFits : Set i
    radiusEightFarHighCoreFits : Set i
    fixedAbsoluteFloorRouteRefuted : Set i

open ExactFiniteCertificateCore public

record PeriodicFourierTailObligations (i : Level) : Set (lsuc i) where
  field
    Index Shell Time State : Set i

    AdjacentEstimate : Index → Shell → Time → State → Set i
    GeometricRemainderEstimate : Index → Shell → Time → State → Set i
    NearTriadAbsorption : Index → Shell → Time → State → Set i
    RadiusEightFarLow : Index → Shell → Time → State → Set i
    RadiusEightFarHigh : Index → Shell → Time → State → Set i
    RealCarrierInwardnessAndCoercivity : Index → Time → State → Set i
    OfficialDataCoverage : State → Set i

    adjacentEstimateAll : ∀ q K τ u → AdjacentEstimate q K τ u
    geometricRemainderAll : ∀ q K τ u → GeometricRemainderEstimate q K τ u
    nearTriadAbsorptionAll : ∀ q K τ u → NearTriadAbsorption q K τ u
    radiusEightFarLowAll : ∀ q K τ u → RadiusEightFarLow q K τ u
    radiusEightFarHighAll : ∀ q K τ u → RadiusEightFarHigh q K τ u
    realCarrierAll : ∀ q τ u → RealCarrierInwardnessAndCoercivity q τ u
    officialCoverageAll : ∀ u → OfficialDataCoverage u

open PeriodicFourierTailObligations public

record CheckedCertificateWithAnalyticTail (i : Level) : Set (lsuc i) where
  field
    finiteCore : ExactFiniteCertificateCore i
    analyticTail : PeriodicFourierTailObligations i

open CheckedCertificateWithAnalyticTail public

checkedCertificateSuppliesAdjacentEstimate :
  ∀ {i} (C : CheckedCertificateWithAnalyticTail i) →
  ∀ q K τ u → AdjacentEstimate (analyticTail C) q K τ u
checkedCertificateSuppliesAdjacentEstimate C =
  adjacentEstimateAll (analyticTail C)

checkedCertificateSuppliesGeometricRemainder :
  ∀ {i} (C : CheckedCertificateWithAnalyticTail i) →
  ∀ q K τ u → GeometricRemainderEstimate (analyticTail C) q K τ u
checkedCertificateSuppliesGeometricRemainder C =
  geometricRemainderAll (analyticTail C)

checkedCertificateSuppliesNearTriadAbsorption :
  ∀ {i} (C : CheckedCertificateWithAnalyticTail i) →
  ∀ q K τ u → NearTriadAbsorption (analyticTail C) q K τ u
checkedCertificateSuppliesNearTriadAbsorption C =
  nearTriadAbsorptionAll (analyticTail C)

checkedCertificateSuppliesRadiusEightLow :
  ∀ {i} (C : CheckedCertificateWithAnalyticTail i) →
  ∀ q K τ u → RadiusEightFarLow (analyticTail C) q K τ u
checkedCertificateSuppliesRadiusEightLow C =
  radiusEightFarLowAll (analyticTail C)

checkedCertificateSuppliesRadiusEightHigh :
  ∀ {i} (C : CheckedCertificateWithAnalyticTail i) →
  ∀ q K τ u → RadiusEightFarHigh (analyticTail C) q K τ u
checkedCertificateSuppliesRadiusEightHigh C =
  radiusEightFarHighAll (analyticTail C)

checkedCertificateSuppliesRealCarrier :
  ∀ {i} (C : CheckedCertificateWithAnalyticTail i) →
  ∀ q τ u → RealCarrierInwardnessAndCoercivity (analyticTail C) q τ u
checkedCertificateSuppliesRealCarrier C =
  realCarrierAll (analyticTail C)

checkedCertificateSuppliesOfficialCoverage :
  ∀ {i} (C : CheckedCertificateWithAnalyticTail i) →
  ∀ u → OfficialDataCoverage (analyticTail C) u
checkedCertificateSuppliesOfficialCoverage C =
  officialCoverageAll (analyticTail C)

-- Explicit authority boundary.  A generated finite certificate alone never
-- promotes the open periodic-Fourier theorem.
generatedCertificateAlonePromotesAnalyticCutset : Bool
generatedCertificateAlonePromotesAnalyticCutset = false

generatedCertificateAlonePromotesGlobalRegularity : Bool
generatedCertificateAlonePromotesGlobalRegularity = false
