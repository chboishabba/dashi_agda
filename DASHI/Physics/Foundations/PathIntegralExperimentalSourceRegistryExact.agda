module DASHI.Physics.Foundations.PathIntegralExperimentalSourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE REGISTRY: path-integral experiments, stationary action,
-- diffraction/source-scale selection, and finite-source Kelvin wakes.
--
-- Author/title/venue/DOI metadata is explicit and every source carries a
-- bounded role.  Experimental support for path-amplitude composition is not
-- promoted into TSFV or an ontology of independent trajectories.
------------------------------------------------------------------------

record SourceReference : Set where
  constructor sourceReference
  field
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    doiOrIdentifier : String
    boundedRole : String

open SourceReference public

feynman1948 : SourceReference
feynman1948 = sourceReference
  "Richard P. Feynman"
  "Space-Time Approach to Non-Relativistic Quantum Mechanics"
  "Reviews of Modern Physics 20, 367-387"
  1948
  "10.1103/RevModPhys.20.367"
  "historical path-integral amplitude/action formulation; not empirical evidence for an ontology of independently real paths"

wenEtAl2023 : SourceReference
wenEtAl2023 = sourceReference
  "Yong-Li Wen; Yunfei Wang; Li-Man Tian; Shanchao Zhang; Jianfeng Li; Jing-Song Du; Hui Yan; Shi-Liang Zhu"
  "Demonstration of the quantum principle of least action with single photons"
  "Nature Photonics 17, 717-722"
  2023
  "10.1038/s41566-023-01212-1"
  "experimental propagator observation and extraction of classical trajectories from propagator extrema in tested single-photon systems; not a proof that every stationary point is a metric minimum"

wenEtAl2026 : SourceReference
wenEtAl2026 = sourceReference
  "Yong-Li Wen; Li-Man Tian; Yunfei Wang; Shanchao Zhang; Chang Li; Jianfeng Li; Enke Wang; Hui Yan; Shi-Liang Zhu"
  "Direct experimental test of Feynman's path integral postulates with single photons"
  "Science Advances"
  2026
  "10.1126/sciadv.aeh1011"
  "direct experimental test of coherent path-amplitude composition and equal-magnitude/action-phase postulates for the reconstructed finite path family; not evidence that reconstructed histories are independent ontological trajectories"

wenEtAl2026Dataset : SourceReference
wenEtAl2026Dataset = sourceReference
  "Yong-Li Wen; Li-Man Tian; Yunfei Wang; Shanchao Zhang; Chang Li; Jianfeng Li; Enke Wang; Hui Yan; Shi-Liang Zhu"
  "Data: Direct experimental test of Feynman's path integral postulates with single photons"
  "Dryad"
  2026
  "10.5061/dryad.x0k6djj14"
  "reproducibility data for more than 1.4 million (17^5) reconstructed path amplitudes and the reported postulate tests"

bornWolfPrinciplesOfOptics : SourceReference
bornWolfPrinciplesOfOptics = sourceReference
  "Max Born; Emil Wolf"
  "Principles of Optics: Electromagnetic Theory of Propagation, Interference and Diffraction of Light"
  "Cambridge University Press, seventh expanded edition"
  1999
  "10.1017/CBO9781139644181"
  "classical optics authority for interference, diffraction, aperture-scale dependence, and stationary-phase/steepest-descent methods; supports the optics consumer role only and does not identify aperture diffraction with Kelvin-wake physics"

rabaudMoisy2013 : SourceReference
rabaudMoisy2013 = sourceReference
  "Marc Rabaud; Frederic Moisy"
  "Ship Wakes: Kelvin or Mach Angle?"
  "Physical Review Letters 110, 214503"
  2013
  "10.1103/PhysRevLett.110.214503"
  "finite-size/Froude-number dependence of apparent wake angle at high speed; distinguishes visible dominant wake from the ideal point-source Kelvin prediction"

darmonBenzaquenRaphael2014 : SourceReference
darmonBenzaquenRaphael2014 = sourceReference
  "Alexandre Darmon; Michael Benzaquen; Elie Raphael"
  "Kelvin wake pattern at large Froude numbers"
  "Journal of Fluid Mechanics 738, R3"
  2014
  "10.1017/jfm.2013.607"
  "stationary-phase finite-source analysis: maximum-amplitude wake angle can scale as Fr^-1 while the outer Kelvin wake boundary remains at the Kelvin angle"

record SourceRegistryBoundary : Set where
  constructor sourceRegistryBoundary
  field
    authorMetadataInstalled : Bool
    titleMetadataInstalled : Bool
    doiMetadataInstalled : Bool
    empiricalRoleBounded : Bool
    tsfvPromotionFromSources : Bool
    tsfvPromotionFromSourcesIsFalse : tsfvPromotionFromSources ≡ false

canonicalSourceRegistryBoundary : SourceRegistryBoundary
canonicalSourceRegistryBoundary =
  sourceRegistryBoundary true true true true false refl
