module DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneSplitFibreExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact as Executable
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact as Physical

------------------------------------------------------------------------
-- A concrete physical split-coordinate realization at the first nontrivial
-- centred odd scale.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- We choose r = 1, hence L = 2r+1 = 3 and |B_r| = 3^4 = 81.  A fine
-- site is represented by a coarse site together with its unique centred block
-- coordinate.  This makes the projection fibre and endpoint-block statements
-- constructor-level facts rather than external cardinality assumptions.
------------------------------------------------------------------------

one three eightyOne : Nat
one = suc zero
three = suc (suc (suc zero))
eightyOne = (three * three) * (three * three)

radiusOneSideExact : Centered.oddSide one ≡ three
radiusOneSideExact = refl

radiusOneVolumeExact :
  Centered.fourthPower (Centered.oddSide one) ≡ eightyOne
radiusOneVolumeExact = refl

SplitFineSite : Nat → Set → Set
SplitFineSite radius CoarseSite =
  Carrier.Product CoarseSite (Centered.CenteredBlockPoint4 radius)

splitProject :
  ∀ {radius CoarseSite} → SplitFineSite radius CoarseSite → CoarseSite
splitProject (Carrier.pair coarse point) = coarse

splitEmbed :
  ∀ {radius CoarseSite} →
  CoarseSite → Centered.CenteredBlockPoint4 radius →
  SplitFineSite radius CoarseSite
splitEmbed coarse point = Carrier.pair coarse point

splitEmbedProjects :
  ∀ {radius CoarseSite} coarse point →
  splitProject (splitEmbed {radius = radius} coarse point) ≡ coarse
splitEmbedProjects coarse point = refl

splitProjectionFibreComplete :
  ∀ {radius CoarseSite}
    (coarse : CoarseSite) (site : SplitFineSite radius CoarseSite) →
  splitProject site ≡ coarse →
  Physical.CenteredPreimage (splitEmbed coarse) site
splitProjectionFibreComplete coarse (Carrier.pair .coarse point) refl =
  Physical.centredPreimage point refl

splitEmbedInjective :
  ∀ {radius CoarseSite} coarse
    {left right : Centered.CenteredBlockPoint4 radius} →
  splitEmbed coarse left ≡ splitEmbed coarse right → left ≡ right
splitEmbedInjective coarse = Carrier.productSecondInjective

splitScaleSpacing : Nat → Nat → Nat
splitScaleSpacing side spacing = side * spacing

splitPhysicalScaleGeometry :
  ∀ {radius CoarseSite} →
  Executable.CenteredExecutableGeometry radius →
  (fineSpacing : Nat) →
  Physical.CMP109PhysicalScaleGeometry
    radius (SplitFineSite radius CoarseSite) CoarseSite Nat
splitPhysicalScaleGeometry {radius} executable fineSpacing = record
  { executableGeometry = executable
  ; projectSite = splitProject
  ; embedAt = splitEmbed
  ; embedProjectsToCentre =
      splitEmbedProjects
  ; projectionFibreComplete =
      splitProjectionFibreComplete
  ; embedAtInjective =
      splitEmbedInjective
  ; fineSpacing = fineSpacing
  ; coarseSpacing =
      Centered.oddSide radius * fineSpacing
  ; scaleSpacing = splitScaleSpacing
  ; coarseSpacingMeaning = refl
  }

radiusOneSplitPhysicalScaleDecision :
  ∀ {CoarseSite} (fineSpacing : Nat) →
  Carrier.Dec
    (Physical.CMP109PhysicalScaleGeometry
      one (SplitFineSite one CoarseSite) CoarseSite Nat)
radiusOneSplitPhysicalScaleDecision fineSpacing
  with Executable.centeredExecutableGeometryDecision one
... | Carrier.yes executable =
      Carrier.yes (splitPhysicalScaleGeometry executable fineSpacing)
... | Carrier.no notExecutable = Carrier.no λ geometry →
      notExecutable (Physical.executableGeometry geometry)

radiusOnePhysicalBlockHasEightyOneSites :
  ∀ {CoarseSite}
    (geometry : Physical.CMP109PhysicalScaleGeometry
      one (SplitFineSite one CoarseSite) CoarseSite Nat)
    coarse →
  length (Physical.physicalBlockElements geometry coarse) ≡ eightyOne
radiusOnePhysicalBlockHasEightyOneSites geometry coarse =
  trans
    (Physical.physicalBlockEnumerationLength geometry coarse)
    radiusOneVolumeExact

SplitCoarseBond : Set → Set
SplitCoarseBond CoarseSite = Carrier.Product CoarseSite CoarseSite

SplitFineBond : Nat → Set → Set
SplitFineBond radius CoarseSite =
  Carrier.Product
    (SplitFineSite radius CoarseSite)
    (SplitFineSite radius CoarseSite)

splitEndpointIdentification :
  ∀ {radius CoarseSite}
    (geometry : Physical.CMP109PhysicalScaleGeometry
      radius (SplitFineSite radius CoarseSite) CoarseSite Nat) →
  Physical.CMP109EndpointBlockIdentification
    {FineBond = SplitFineBond radius CoarseSite}
    {CoarseBond = SplitCoarseBond CoarseSite}
    geometry
splitEndpointIdentification geometry = record
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

cmp109RadiusOneSideAndVolumeLevel : ProofLevel
cmp109RadiusOneSideAndVolumeLevel = computed

cmp109SplitProjectionFibreLevel : ProofLevel
cmp109SplitProjectionFibreLevel = machineChecked

cmp109SplitEndpointBlockLevel : ProofLevel
cmp109SplitEndpointBlockLevel = machineChecked

cmp109RadiusOnePhysicalDecisionLevel : ProofLevel
cmp109RadiusOnePhysicalDecisionLevel = computed
