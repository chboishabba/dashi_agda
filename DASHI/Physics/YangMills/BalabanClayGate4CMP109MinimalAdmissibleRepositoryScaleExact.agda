module DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤ᵇ_)
open import Data.Rational using (ℚ; 1ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact as Executable
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredTorusBijectionExact as Bijection
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact as Physical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneRepositoryTorusExact as RepositoryBijection

------------------------------------------------------------------------
-- Minimal source-admissible CMP109 scale on the repository torus.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The geometric setup preceding equation (0.1) requires L to be an odd
-- positive integer strictly greater than 11. The minimal choice is therefore
--
--   L = 13, r = 6, L = 2r+1, |B_r| = 13^4 = 28561.
--
-- The coarse torus below has one site and the fine repository torus has side
-- 13. This is the smallest literal finite-volume CMP109 carrier satisfying
-- the source scale hypothesis.
------------------------------------------------------------------------

radius side volume : Nat
radius = 6
side = 13
volume = 28561

sideIsOddRadius : Centered.oddSide radius ≡ side
sideIsOddRadius = refl

sideAboveEleven : 12 ≤ᵇ side ≡ true
sideAboveEleven = refl

volumeExact :
  Centered.fourthPower (Centered.oddSide radius) ≡ volume
volumeExact = refl

RepositoryCoarseSite : Set
RepositoryCoarseSite = Carrier.periodicTorus4Definition 1

RepositoryFineSite : Set
RepositoryFineSite =
  Blocks.PeriodicBlock (Bijection.centeredTorusParameter radius)

repositoryCoarseOrigin : RepositoryCoarseSite
repositoryCoarseOrigin =
  Carrier.pair
    (Carrier.pair Carrier.zeroᵢ Carrier.zeroᵢ)
    (Carrier.pair Carrier.zeroᵢ Carrier.zeroᵢ)

repositoryCoarseUnique : ∀ coarse → coarse ≡ repositoryCoarseOrigin
repositoryCoarseUnique
  (Carrier.pair
    (Carrier.pair Carrier.zeroᵢ Carrier.zeroᵢ)
    (Carrier.pair Carrier.zeroᵢ Carrier.zeroᵢ)) = refl

repositoryProject : RepositoryFineSite → RepositoryCoarseSite
repositoryProject site = repositoryCoarseOrigin

repositoryEmbedAt :
  RepositoryCoarseSite → Centered.CenteredBlockPoint4 radius →
  RepositoryFineSite
repositoryEmbedAt coarse point = Bijection.directCenteredEmbed point

repositoryEmbedProjects : ∀ coarse point →
  repositoryProject (repositoryEmbedAt coarse point) ≡ coarse
repositoryEmbedProjects coarse point = sym (repositoryCoarseUnique coarse)

repositoryProjectionFibreComplete : ∀ coarse site →
  repositoryProject site ≡ coarse →
  Physical.CenteredPreimage (repositoryEmbedAt coarse) site
repositoryProjectionFibreComplete coarse site projects =
  Physical.centredPreimage
    (Bijection.directCenteredDecode site)
    (RepositoryBijection.directCenteredEncodeDecode site)

repositoryEmbedInjective : ∀ coarse {left right} →
  repositoryEmbedAt coarse left ≡ repositoryEmbedAt coarse right →
  left ≡ right
repositoryEmbedInjective coarse = Bijection.directCenteredEmbedInjective

minimalAdmissiblePhysicalGeometry :
  Executable.CenteredExecutableGeometry radius →
  Physical.CMP109PhysicalScaleGeometry
    radius RepositoryFineSite RepositoryCoarseSite Nat
minimalAdmissiblePhysicalGeometry executable = record
  { Physical.CMP109PhysicalScaleGeometry.executableGeometry = executable
  ; Physical.CMP109PhysicalScaleGeometry.projectSite = repositoryProject
  ; Physical.CMP109PhysicalScaleGeometry.embedAt = repositoryEmbedAt
  ; Physical.CMP109PhysicalScaleGeometry.embedProjectsToCentre =
      repositoryEmbedProjects
  ; Physical.CMP109PhysicalScaleGeometry.projectionFibreComplete =
      repositoryProjectionFibreComplete
  ; Physical.CMP109PhysicalScaleGeometry.embedAtInjective =
      repositoryEmbedInjective
  ; Physical.CMP109PhysicalScaleGeometry.fineSpacing = 1
  ; Physical.CMP109PhysicalScaleGeometry.coarseSpacing = side
  ; Physical.CMP109PhysicalScaleGeometry.scaleSpacing = _*_
  ; Physical.CMP109PhysicalScaleGeometry.coarseSpacingMeaning = refl
  }

minimalAdmissibleGeometryDecision :
  Carrier.Dec
    (Physical.CMP109PhysicalScaleGeometry
      radius RepositoryFineSite RepositoryCoarseSite Nat)
minimalAdmissibleGeometryDecision
  with Executable.centeredExecutableGeometryDecision radius
... | Carrier.yes executable =
      Carrier.yes (minimalAdmissiblePhysicalGeometry executable)
... | Carrier.no notExecutable = Carrier.no λ geometry →
      notExecutable (Physical.executableGeometry geometry)

RepositoryCoarseBond : Set
RepositoryCoarseBond = Carrier.Product RepositoryCoarseSite RepositoryCoarseSite

RepositoryFineBond : Set
RepositoryFineBond = Carrier.Product RepositoryFineSite RepositoryFineSite

minimalAdmissibleEndpointIdentification :
  (geometry : Physical.CMP109PhysicalScaleGeometry
    radius RepositoryFineSite RepositoryCoarseSite Nat) →
  Physical.CMP109EndpointBlockIdentification
    {FineBond = RepositoryFineBond}
    {CoarseBond = RepositoryCoarseBond}
    geometry
minimalAdmissibleEndpointIdentification geometry = record
  { Physical.CMP109EndpointBlockIdentification.source = Carrier.first
  ; Physical.CMP109EndpointBlockIdentification.target = Carrier.second
  ; Physical.CMP109EndpointBlockIdentification.fineSource = Carrier.first
  ; Physical.CMP109EndpointBlockIdentification.fineTarget = Carrier.second
  ; Physical.CMP109EndpointBlockIdentification.CrossingFineBond =
      λ coarse fine → Carrier.Product
        (Physical.projectSite geometry (Carrier.first fine)
          ≡ Carrier.first coarse)
        (Physical.projectSite geometry (Carrier.second fine)
          ≡ Carrier.second coarse)
  ; Physical.CMP109EndpointBlockIdentification.crossingSourceProjects =
      λ coarse fine crossing → Carrier.first crossing
  ; Physical.CMP109EndpointBlockIdentification.crossingTargetProjects =
      λ coarse fine crossing → Carrier.second crossing
  }

volumeℚ siteWeightℚ : ℚ
volumeℚ = + 28561 / 1
siteWeightℚ = + 1 / 28561

minimalSiteWeightCancelsVolume : ∀ value →
  siteWeightℚ * (volumeℚ * value) ≡ value
minimalSiteWeightCancelsVolume = ℚRing.solve-∀

minimalSiteWeightIsReciprocal : siteWeightℚ * volumeℚ ≡ 1ℚ
minimalSiteWeightIsReciprocal = minimalSiteWeightCancelsVolume 1ℚ

cmp109MinimalOddScaleAdmissibilityLevel : ProofLevel
cmp109MinimalOddScaleAdmissibilityLevel = computed

cmp109MinimalRepositoryProjectionLevel : ProofLevel
cmp109MinimalRepositoryProjectionLevel = machineChecked

cmp109MinimalRepositoryEndpointLevel : ProofLevel
cmp109MinimalRepositoryEndpointLevel = machineChecked

cmp109MinimalSiteWeightLevel : ProofLevel
cmp109MinimalSiteWeightLevel = machineChecked

cmp109MinimalGeometryDecisionLevel : ProofLevel
cmp109MinimalGeometryDecisionLevel = computed
