module DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneRepositoryTorusExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
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
joinIndex {leftSize} {rightSize} (Bijection.fromLeft index) =
  Bijection.injectLeftIndex {leftSize} {rightSize} index
joinIndex {leftSize} {rightSize} (Bijection.fromRight index) =
  Bijection.injectRightIndex {leftSize} {rightSize} index

joinSplitIndex :
  ∀ {leftSize rightSize}
    (index : Carrier.CyclicIndex (leftSize + rightSize)) →
  joinIndex {leftSize} {rightSize} (Bijection.splitIndex {leftSize} {rightSize} index) ≡ index
joinSplitIndex {zero} index = refl
joinSplitIndex {suc leftSize} Carrier.zeroᵢ = refl
joinSplitIndex {suc leftSize} {rightSize} (Carrier.sucᵢ index)
  with Bijection.splitIndex {leftSize} {rightSize} index
    | joinSplitIndex {leftSize} {rightSize} index
... | Bijection.fromLeft left | refl = refl
... | Bijection.fromRight right | refl = refl

centeredOffsetEncodeDecode :
  ∀ {radius}
    (index : Carrier.CyclicIndex (suc (radius + radius))) →
  Bijection.centeredOffsetIndex {radius}
    (Bijection.centeredOffsetFromIndex {radius} index)
  ≡ index
centeredOffsetEncodeDecode Carrier.zeroᵢ = refl
centeredOffsetEncodeDecode {radius} (Carrier.sucᵢ index)
  with Bijection.splitIndex {radius} {radius} index
    | joinSplitIndex {radius} {radius} index
... | Bijection.fromLeft left | refl = refl
... | Bijection.fromRight right | refl
  rewrite Bijection.reverseFiniteIndexInvolutive right = refl

directCenteredEncodeDecode :
  ∀ {radius}
    (site : Blocks.PeriodicBlock (Bijection.centeredTorusParameter radius)) →
  Bijection.directCenteredEmbed {radius}
    (Bijection.directCenteredDecode {radius} site)
  ≡ site
directCenteredEncodeDecode {radius}
    (Carrier.pair (Carrier.pair index0 index1)
      (Carrier.pair index2 index3)) =
  Bijection.pairCong
    (Bijection.pairCong
      (centeredOffsetEncodeDecode {radius} index0)
      (centeredOffsetEncodeDecode {radius} index1))
    (Bijection.pairCong
      (centeredOffsetEncodeDecode {radius} index2)
      (centeredOffsetEncodeDecode {radius} index3))

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
  { executableGeometry = executable
  ; projectSite = repositoryProject
  ; embedAt = repositoryEmbedAt
  ; embedProjectsToCentre =
      repositoryEmbedProjects
  ; projectionFibreComplete =
      repositoryProjectionFibreComplete
  ; embedAtInjective =
      repositoryEmbedInjective
  ; fineSpacing = suc zero
  ; coarseSpacing = RadiusOne.three
  ; scaleSpacing = _*_
  ; coarseSpacingMeaning = refl
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
  { source = Carrier.first
  ; target = Carrier.second
  ; fineSource = Carrier.first
  ; fineTarget = Carrier.second
  ; CrossingFineBond =
      λ coarse fine → Carrier.Product
        (Physical.projectSite geometry (Carrier.first fine)
          ≡ Carrier.first coarse)
        (Physical.projectSite geometry (Carrier.second fine)
          ≡ Carrier.second coarse)
  ; crossingSourceProjects =
      λ coarse fine crossing → Carrier.first crossing
  ; crossingTargetProjects =
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
