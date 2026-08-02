module DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneRepositoryTorusExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact as Executable
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredTorusBijectionExact as Bijection
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact as Physical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneSplitFibreExact as RadiusOne

------------------------------------------------------------------------
-- Literal repository-torus realization of the selected r=1, L=3 block.
--
-- The coarse torus has side one and therefore one site. The fine torus has
-- side three and is exactly the repository `PeriodicBlock 2`. The centred
-- block map is upgraded here from a proved injection to a two-sided bijection.
------------------------------------------------------------------------

joinIndex :
  ∀ {leftSize rightSize} →
  Bijection.IndexSplit leftSize rightSize →
  Carrier.CyclicIndex (leftSize + rightSize)
joinIndex (Bijection.fromLeft index) = Bijection.injectLeftIndex index
joinIndex (Bijection.fromRight index) = Bijection.injectRightIndex index

joinSplitIndex :
  ∀ {leftSize rightSize}
    (index : Carrier.CyclicIndex (leftSize + rightSize)) →
  joinIndex (Bijection.splitIndex index) ≡ index
joinSplitIndex {zero} index = refl
joinSplitIndex {suc leftSize} Carrier.zeroᵢ = refl
joinSplitIndex {suc leftSize} (Carrier.sucᵢ index)
  with Bijection.splitIndex {leftSize} {rightSize} index
... | Bijection.fromLeft left
  rewrite joinSplitIndex {leftSize} {rightSize} index = refl
... | Bijection.fromRight right
  rewrite joinSplitIndex {leftSize} {rightSize} index = refl

centeredOffsetEncodeDecode :
  ∀ {radius}
    (index : Carrier.CyclicIndex (suc (radius + radius))) →
  Bijection.centeredOffsetIndex
    (Bijection.centeredOffsetFromIndex index)
  ≡ index
centeredOffsetEncodeDecode Carrier.zeroᵢ = refl
centeredOffsetEncodeDecode {radius} (Carrier.sucᵢ index)
  with Bijection.splitIndex {radius} {radius} index
... | Bijection.fromLeft left
  rewrite joinSplitIndex {radius} {radius} index = refl
... | Bijection.fromRight right
  rewrite Bijection.reverseFiniteIndexInvolutive right
        | joinSplitIndex {radius} {radius} index = refl

directCenteredEncodeDecode :
  ∀ {radius}
    (site : Blocks.PeriodicBlock (Bijection.centeredTorusParameter radius)) →
  Bijection.directCenteredEmbed
    (Bijection.directCenteredDecode site)
  ≡ site
directCenteredEncodeDecode
    (Carrier.pair (Carrier.pair index0 index1)
      (Carrier.pair index2 index3)) =
  Bijection.pairCong
    (Bijection.pairCong
      (centeredOffsetEncodeDecode index0)
      (centeredOffsetEncodeDecode index1))
    (Bijection.pairCong
      (centeredOffsetEncodeDecode index2)
      (centeredOffsetEncodeDecode index3))

RepositoryCoarseSite : Set
RepositoryCoarseSite = Carrier.periodicTorus4Definition (suc zero)

RepositoryFineSite : Set
RepositoryFineSite = Blocks.PeriodicBlock
  (Bijection.centeredTorusParameter RadiusOne.one)

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
  RepositoryCoarseSite →
  Centered.CenteredBlockPoint4 RadiusOne.one →
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
    (directCenteredEncodeDecode site)

repositoryEmbedInjective : ∀ coarse {left right} →
  repositoryEmbedAt coarse left ≡ repositoryEmbedAt coarse right →
  left ≡ right
repositoryEmbedInjective coarse = Bijection.directCenteredEmbedInjective

repositoryRadiusOnePhysicalGeometry :
  Executable.CenteredExecutableGeometry RadiusOne.one →
  Physical.CMP109PhysicalScaleGeometry
    RadiusOne.one RepositoryFineSite RepositoryCoarseSite Nat
repositoryRadiusOnePhysicalGeometry executable = record
  { Physical.CMP109PhysicalScaleGeometry.executableGeometry = executable
  ; Physical.CMP109PhysicalScaleGeometry.projectSite = repositoryProject
  ; Physical.CMP109PhysicalScaleGeometry.embedAt = repositoryEmbedAt
  ; Physical.CMP109PhysicalScaleGeometry.embedProjectsToCentre =
      repositoryEmbedProjects
  ; Physical.CMP109PhysicalScaleGeometry.projectionFibreComplete =
      repositoryProjectionFibreComplete
  ; Physical.CMP109PhysicalScaleGeometry.embedAtInjective =
      repositoryEmbedInjective
  ; Physical.CMP109PhysicalScaleGeometry.fineSpacing = suc zero
  ; Physical.CMP109PhysicalScaleGeometry.coarseSpacing = RadiusOne.three
  ; Physical.CMP109PhysicalScaleGeometry.scaleSpacing = _*_
  ; Physical.CMP109PhysicalScaleGeometry.coarseSpacingMeaning = refl
  }

repositoryRadiusOneGeometryDecision :
  Carrier.Dec
    (Physical.CMP109PhysicalScaleGeometry
      RadiusOne.one RepositoryFineSite RepositoryCoarseSite Nat)
repositoryRadiusOneGeometryDecision
  with Executable.centeredExecutableGeometryDecision RadiusOne.one
... | Carrier.yes executable =
      Carrier.yes (repositoryRadiusOnePhysicalGeometry executable)
... | Carrier.no notExecutable = Carrier.no λ geometry →
      notExecutable (Physical.executableGeometry geometry)

RepositoryCoarseBond : Set
RepositoryCoarseBond = Carrier.Product RepositoryCoarseSite RepositoryCoarseSite

RepositoryFineBond : Set
RepositoryFineBond = Carrier.Product RepositoryFineSite RepositoryFineSite

repositoryEndpointIdentification :
  (geometry : Physical.CMP109PhysicalScaleGeometry
    RadiusOne.one RepositoryFineSite RepositoryCoarseSite Nat) →
  Physical.CMP109EndpointBlockIdentification
    {FineBond = RepositoryFineBond}
    {CoarseBond = RepositoryCoarseBond}
    geometry
repositoryEndpointIdentification geometry = record
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

cmp109CenteredTorusSurjectionLevel : ProofLevel
cmp109CenteredTorusSurjectionLevel = machineChecked

cmp109RadiusOneRepositoryProjectionLevel : ProofLevel
cmp109RadiusOneRepositoryProjectionLevel = machineChecked

cmp109RadiusOneRepositoryEndpointLevel : ProofLevel
cmp109RadiusOneRepositoryEndpointLevel = machineChecked

cmp109RadiusOneRepositoryGeometryDecisionLevel : ProofLevel
cmp109RadiusOneRepositoryGeometryDecisionLevel = computed
