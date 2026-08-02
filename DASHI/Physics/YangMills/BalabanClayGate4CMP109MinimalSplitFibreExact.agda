module DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalSplitFibreExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact as Executable
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact as Physical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal

------------------------------------------------------------------------
-- Arbitrary-coarse-site realization of the minimal CMP109 projection fibre.
--
-- FineSite = CoarseSite x B_6.
--
-- This carrier is definitionally a disjoint union of 28,561-site centred
-- blocks. It closes the projection-fibre and endpoint geometry for an arbitrary
-- coarse lattice without pretending that the remaining mixed-radix equivalence
-- with `PeriodicTorus4 (13*N)` is definitional.
------------------------------------------------------------------------

MinimalSplitFineSite : Set → Set
MinimalSplitFineSite CoarseSite =
  Carrier.Product CoarseSite (Centered.CenteredBlockPoint4 Minimal.radius)

minimalSplitProject :
  ∀ {CoarseSite : Set} → MinimalSplitFineSite CoarseSite → CoarseSite
minimalSplitProject = Carrier.first

minimalSplitEmbedAt :
  ∀ {CoarseSite : Set} →
  CoarseSite → Centered.CenteredBlockPoint4 Minimal.radius →
  MinimalSplitFineSite CoarseSite
minimalSplitEmbedAt coarse point = Carrier.pair coarse point

minimalSplitEmbedProjects :
  ∀ {CoarseSite : Set} coarse point →
  minimalSplitProject (minimalSplitEmbedAt coarse point) ≡ coarse
minimalSplitEmbedProjects coarse point = refl

minimalSplitProjectionFibreComplete :
  ∀ {CoarseSite : Set} coarse site →
  minimalSplitProject site ≡ coarse →
  Physical.CenteredPreimage (minimalSplitEmbedAt coarse) site
minimalSplitProjectionFibreComplete coarse (Carrier.pair siteCoarse point) projects
  rewrite projects = Physical.centredPreimage point refl

minimalSplitEmbedInjective :
  ∀ {CoarseSite : Set} coarse {left right} →
  minimalSplitEmbedAt coarse left ≡ minimalSplitEmbedAt coarse right →
  left ≡ right
minimalSplitEmbedInjective coarse equality =
  cong Carrier.second equality

minimalSplitPhysicalGeometry :
  ∀ {CoarseSite : Set} →
  Executable.CenteredExecutableGeometry Minimal.radius →
  Nat →
  Physical.CMP109PhysicalScaleGeometry
    Minimal.radius (MinimalSplitFineSite CoarseSite) CoarseSite Nat
minimalSplitPhysicalGeometry executable fineSpacing = record
  { Physical.CMP109PhysicalScaleGeometry.executableGeometry = executable
  ; Physical.CMP109PhysicalScaleGeometry.projectSite = minimalSplitProject
  ; Physical.CMP109PhysicalScaleGeometry.embedAt = minimalSplitEmbedAt
  ; Physical.CMP109PhysicalScaleGeometry.embedProjectsToCentre =
      minimalSplitEmbedProjects
  ; Physical.CMP109PhysicalScaleGeometry.projectionFibreComplete =
      minimalSplitProjectionFibreComplete
  ; Physical.CMP109PhysicalScaleGeometry.embedAtInjective =
      minimalSplitEmbedInjective
  ; Physical.CMP109PhysicalScaleGeometry.fineSpacing = fineSpacing
  ; Physical.CMP109PhysicalScaleGeometry.coarseSpacing =
      Minimal.side * fineSpacing
  ; Physical.CMP109PhysicalScaleGeometry.scaleSpacing = _*_
  ; Physical.CMP109PhysicalScaleGeometry.coarseSpacingMeaning = refl
  }

minimalSplitGeometryDecision :
  ∀ {CoarseSite : Set} fineSpacing →
  Carrier.Dec
    (Physical.CMP109PhysicalScaleGeometry
      Minimal.radius (MinimalSplitFineSite CoarseSite) CoarseSite Nat)
minimalSplitGeometryDecision fineSpacing
  with Executable.centeredExecutableGeometryDecision Minimal.radius
... | Carrier.yes executable =
      Carrier.yes (minimalSplitPhysicalGeometry executable fineSpacing)
... | Carrier.no notExecutable = Carrier.no λ geometry →
      notExecutable (Physical.executableGeometry geometry)

MinimalSplitCoarseBond : Set → Set
MinimalSplitCoarseBond CoarseSite = Carrier.Product CoarseSite CoarseSite

MinimalSplitFineBond : Set → Set
MinimalSplitFineBond CoarseSite =
  Carrier.Product
    (MinimalSplitFineSite CoarseSite)
    (MinimalSplitFineSite CoarseSite)

minimalSplitEndpointIdentification :
  ∀ {CoarseSite : Set}
    (geometry : Physical.CMP109PhysicalScaleGeometry
      Minimal.radius (MinimalSplitFineSite CoarseSite) CoarseSite Nat) →
  Physical.CMP109EndpointBlockIdentification
    {FineBond = MinimalSplitFineBond CoarseSite}
    {CoarseBond = MinimalSplitCoarseBond CoarseSite}
    geometry
minimalSplitEndpointIdentification geometry = record
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

cmp109MinimalSplitProjectionFibreLevel : ProofLevel
cmp109MinimalSplitProjectionFibreLevel = machineChecked

cmp109MinimalSplitEndpointLevel : ProofLevel
cmp109MinimalSplitEndpointLevel = machineChecked

cmp109MinimalSplitGeometryDecisionLevel : ProofLevel
cmp109MinimalSplitGeometryDecisionLevel = computed

physicalMinimalSplitToPeriodicTorusEquivalenceInputsLevel : ProofLevel
physicalMinimalSplitToPeriodicTorusEquivalenceInputsLevel = conditional
