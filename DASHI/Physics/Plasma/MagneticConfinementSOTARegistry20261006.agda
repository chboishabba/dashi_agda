module DASHI.Physics.Plasma.MagneticConfinementSOTARegistry20261006 where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED SOTA REGISTRY -- snapshot 2026-10-06
--
-- These are provenance-bounded public claims used to shape formal obligations.
-- They are not promoted to universal reactor laws or same-regime transfer.
------------------------------------------------------------------------

record SOTASourceClaim : Set where
  constructor sota-source-claim
  field
    programme : String
    architecture : String
    claim : String
    source : String
    accessSnapshot : String

open SOTASourceClaim public

westLongPulse : SOTASourceClaim
westLongPulse = sota-source-claim
  "WEST / CEA-IRFM"
  "tungsten-wall tokamak"
  "1337 s hydrogen plasma with 2.6 GJ injected/extracted energy was reported for 12 February 2025; 2026 C13 later reached first H-mode plasmas with ELMs and continued tungsten, exhaust and wall-interaction studies"
  "https://irfm.cea.fr/en/2025/02/west-sets-a-new-plasma-duration-record/ ; https://irfm.cea.fr/en/2026/08/west-concludes-the-c13-campaign-with-a-major-milestone-first-h-mode-plasmas-with-elms-2/"
  "2026-10-06"

hh70HTSLongPulse : SOTASourceClaim
hh70HTSLongPulse = sota-source-claim
  "Energy Singularity HH70"
  "all-HTS compact tokamak"
  "first plasma in 2024; company reports 1337 s long-pulse operation in February 2026 using AI feedback, RF current drive, lithium wall conditioning and water-cooled plasma-facing components"
  "https://energysingularity.cn/en/news/news-025.html ; https://energysingularity.cn/en/news/news-001.html"
  "2026-10-06"

hh170Target : SOTASourceClaim
hh170Target = sota-source-claim
  "Energy Singularity HH170"
  "high-field all-HTS compact tokamak"
  "public device roadmap lists approximately 10 T centre field, 1.5 m major radius and equivalent Q target above 2"
  "https://energysingularity.cn/en/devices.html"
  "2026-10-06"

exl50uSphericalTorus : SOTASourceClaim
exl50uSphericalTorus = sota-source-claim
  "ENN EXL-50U"
  "spherical torus proton-boron programme"
  "ENN reports 1 MA plasma current, 1.2 T central toroidal field for seconds, electron temperature around 100 million degrees, ion temperature around 50 million degrees and H-mode operation; EHL-2 is the next-step device"
  "https://en.ennresearch.com/News/2026/0403/747.html ; https://en.ennresearch.com/researchfield/Compactfusion/Experiment/ ; https://en.ennresearch.com/researchfield/Compactfusion/EHL_2/"
  "2026-10-06"

w7xLongPulseTripleProduct : SOTASourceClaim
w7xLongPulseTripleProduct = sota-source-claim
  "Wendelstein 7-X / IPP"
  "optimized stellarator"
  "IPP reports a world-best triple product for long plasma durations sustained for 43 s in the 2025 OP2.3 campaign; 2026 work continues toward steady-state power-plant-relevant heating and confinement"
  "https://www.ipp.mpg.de/5532945/w7x ; https://www.ipp.mpg.de/hipmib26en"
  "2026-10-06"

stepCommercialObjective : SOTASourceClaim
stepCommercialObjective = sota-source-claim
  "UK STEP"
  "spherical tokamak prototype power plant"
  "STEP targets 100 MW net electric power, tritium self-sufficiency, high-grade heat and a route to commercial plant availability rather than plasma performance alone"
  "https://scientific-publications.ukaea.uk/papers/sizing-the-step-prototype-powerplant/"
  "2026-10-06"

greenwaldHighDensityDIIID : SOTASourceClaim
greenwaldHighDensityDIIID = sota-source-claim
  "DIII-D high-poloidal-beta regime"
  "advanced tokamak operating scenario"
  "Nature 2024 reports stable plasmas above the line-averaged Greenwald density together with confinement above standard H-mode and small edge transients"
  "https://www.nature.com/articles/s41586-024-07313-3"
  "2026-10-06"

greenwaldMSTExtended : SOTASourceClaim
greenwaldMSTExtended = sota-source-claim
  "Madison Symmetric Torus"
  "current-carrying toroidal plasma with conducting-wall stabilization"
  "Physical Review Letters 2024 reports density up to about ten times the Greenwald value in a device/regime not directly transferable to a fusion power plant"
  "https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.133.055101"
  "2026-10-06"

omnigenousUmbilic : SOTASourceClaim
omnigenousUmbilic = sota-source-claim
  "Gaur et al. omnigenous umbilic stellarators"
  "omnigenous high-curvature twisted-boundary stellarator family"
  "2025/2026 work constructs finite-beta and vacuum omnigenous configurations whose trapped-particle confinement is assessed with second-adiabatic-invariant structure; some boundaries exhibit a strongly twisted Mobius-like appearance"
  "https://www.cambridge.org/core/journals/journal-of-plasma-physics/article/omnigenous-umbilic-stellarators/9B2DA755935A20E123403AACC45833CA ; https://arxiv.org/abs/2505.04211"
  "2026-10-06"

maximumJQI : SOTASourceClaim
maximumJQI = sota-source-claim
  "maximum-J quasi-isodynamic stellarator literature"
  "quasi-isodynamic / omnigenous trapped-particle optimization"
  "maximum-J strengthens an omnigenous trapped-particle target by requiring favorable radial dependence of the second adiabatic invariant; ideal omnigenity requires negligible field-line-label dependence of J_parallel"
  "https://www.cambridge.org/core/journals/journal-of-plasma-physics/article/maximumj-property-in-quasiisodynamic-stellarators/4691B14FC2713173CD8AB2490649761A ; https://www.cambridge.org/core/journals/journal-of-plasma-physics/article/magnetic-fields-with-general-omnigenity/8E3A81AF1CCBBB9CFBC9F3B0EFF6053D"
  "2026-10-06"

record SOTARegistryBoundary : Set where
  constructor sota-registry-boundary
  field
    sourceClaimIsUniversalLaw : Bool
    sourceClaimIsUniversalLawIsFalse : sourceClaimIsUniversalLaw ≡ false
    recordPerformanceTransfersAcrossArchitecture : Bool
    recordPerformanceTransfersAcrossArchitectureIsFalse :
      recordPerformanceTransfersAcrossArchitecture ≡ false
    commercialTargetMustRemainPlantLevel : Bool
    commercialTargetMustRemainPlantLevelIsTrue :
      commercialTargetMustRemainPlantLevel ≡ true

canonicalSOTARegistryBoundary : SOTARegistryBoundary
canonicalSOTARegistryBoundary =
  sota-registry-boundary false refl false refl true refl
