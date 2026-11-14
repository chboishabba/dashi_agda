module DASHI.Physics.Thermodynamics.MagnothermPolarisEvidenceExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Peer-reviewed POLARIS system evidence.
--
-- The 2026 POLARIS paper is device/system evidence for MAGNOTHERM's beverage
-- cooler platform.  Its optimized reported configuration uses Gd/GdEr rather
-- than the LaFeSi material in the 2025 corrosion study, so it must not be used
-- as same-material LaFeSi COP/capacity/lifetime payment.
------------------------------------------------------------------------

polaris2026 : Source.AttributedSource
polaris2026 =
  Source.mkDOISource
    "Jierong Liang; Jeffrey Pickett; Sarah Hermann; Tim Sittig; Thomas Reichert; Martin Lehmann; Jonas Stötzer; Jens-Peter Zwick; Max Greifenstein; Milan Strauch; Konstantin Skokov; Oliver Gutfleisch; Tino Gottschall; Maximilian Fries; Dimitri Benke"
    "Polaris: from laboratory prototypes to market-ready sustainable magnetic beverage coolers"
    "Applied Thermal Engineering 284(1):129144"
    "2026"
    "10.1016/j.applthermaleng.2025.129144"
    "https://doi.org/10.1016/j.applthermaleng.2025.129144"
    Source.academicArticleSource
    "peer-reviewed same-platform system evidence for POLARIS cooling/COP, hydraulic and deployment measurements; optimized working material is Gd/GdEr, so it does not pay LaFeSi same-material performance"
    Source.publicAttribution

data MaterialRelation : Set where
  samePlatformDifferentWorkingMaterial : MaterialRelation
  exactLaFeSiMaterialNotEstablished : MaterialRelation

data PolarisClaimRole : Set where
  devicePerformanceObservation : PolarisClaimRole
  hydraulicSystemObservation : PolarisClaimRole
  commercializationObservation : PolarisClaimRole

record PolarisClaimPayment : Set where
  constructor polarisClaimPayment
  field
    claimLabel : String
    source : Source.AttributedSource
    exactLocator : String
    role : PolarisClaimRole
    materialRelation : MaterialRelation
    empiricalPayment : Bool
    claimCeiling : String

optimizedPolarisPerformancePayment : PolarisClaimPayment
optimizedPolarisPerformancePayment =
  polarisClaimPayment
    "optimized POLARIS configuration reports 131 W/kg specific cooling capacity, plug-in COP 1.0 and 5.4% second-law efficiency at a 15 K span; maximum span 28.5 K is also reported"
    polaris2026
    "Abstract; performance campaign; COP/specific cooling-capacity results"
    devicePerformanceObservation
    samePlatformDifferentWorkingMaterial
    true
    "peer-reviewed POLARIS system performance for the reported Gd/GdEr configuration; not LaFeSi same-material COP/capacity and not STELLAR performance"

polarisHydraulicCampaignPayment : PolarisClaimPayment
polarisHydraulicCampaignPayment =
  polarisClaimPayment
    "POLARIS development includes dedicated energetic, hydraulic, acoustic and material characterization, with flow/utilization and pressure/temperature instrumentation used in optimization"
    polaris2026
    "Measurement campaign; hydraulic test stand; utilization-factor optimization"
    hydraulicSystemObservation
    samePlatformDifferentWorkingMaterial
    true
    "pays the existence and use of a system hydraulic measurement campaign for POLARIS; does not provide hydraulic closure for the exact LaFeSi corrosion-study regenerator"

polarisCommercialDeploymentPayment : PolarisClaimPayment
polarisCommercialDeploymentPayment =
  polarisClaimPayment
    "43 commercial units are reported deployed, with months-long supermarket operation and stable 6 C cooling in reported deployments"
    polaris2026
    "Highlights; Abstract; conclusion"
    commercializationObservation
    samePlatformDifferentWorkingMaterial
    true
    "commercial deployment/TRL evidence for POLARIS; does not prove LaFeSi coating lifetime, LaFeSi COP, or long-duration lifetime for another material stack"

polarisClaimPayments : List PolarisClaimPayment
polarisClaimPayments =
  optimizedPolarisPerformancePayment
  ∷ polarisHydraulicCampaignPayment
  ∷ polarisCommercialDeploymentPayment
  ∷ []

record PolarisEvidenceFirewall : Set where
  constructor polaris-evidence-firewall
  field
    samePlatformIsNotSameWorkingMaterial : Bool
    polarisCOPDoesNotPromoteToLaFeSiCOP : Bool
    polarisHydraulicsDoesNotCloseLaFeSiHydraulics : Bool
    commercialDeploymentDoesNotProveLaFeSiLifetime : Bool
    polarisDoesNotPayStellarPerformance : Bool

canonicalPolarisEvidenceFirewall : PolarisEvidenceFirewall
canonicalPolarisEvidenceFirewall =
  polaris-evidence-firewall true true true true true
