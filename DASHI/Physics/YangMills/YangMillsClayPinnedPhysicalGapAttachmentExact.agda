module DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalGapAttachmentExact where

------------------------------------------------------------------------
-- PHYSICAL CLUSTERING SCALE + SI ATTACHMENT FOR THE PINNED CLAY GAP
--
-- One rational physical rate is used throughout:
--
--   lattice localization exponent
--      -> physical inverse correlation length
--      -> SAME literal Hamiltonian mass-gap magnitude
--      -> SI mass / energy attachment.
--
-- Dimensional/SI correctness is compiler-owned once the physical clustering
-- theorem has supplied the positive inverse correlation length.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact as Scale
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as SI

record PinnedPhysicalClusteringAttachment
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    (G : Top.CompactSimpleGroup C) : Set₁ where
  field
    physicalScale :
      Scale.PhysicalScaleData

    -- The physical rate carried by the clustering conversion is exactly the
    -- literal gap number chosen in the pinned Clay object.
    physicalRateIsLiteralGap :
      Scale.physicalMass physicalScale
      ≡
      Top.massGap
        (Pinned.asLiteralYangMillsConstruction pinned)
        G

    -- Same physical rate is the inverse-correlation-length magnitude used by
    -- the SI endpoint.  This is attachment, not a proof of clustering.
    physicalRateIsSIInverseCorrelationLength :
      Scale.physicalMass physicalScale
      ≡
      SI.magnitude
        (SI.inverseCorrelationLength
          (Pinned.siScales (Pinned.gap pinned) G))

open PinnedPhysicalClusteringAttachment public

literalGapIsPhysicalRate :
  ∀ {C S}
    {pinned : Pinned.PinnedYangMillsConstruction {C = C} S}
    {G : Top.CompactSimpleGroup C} →
  PinnedPhysicalClusteringAttachment pinned G →
  Top.massGap
    (Pinned.asLiteralYangMillsConstruction pinned)
    G
  ≡
  Scale.physicalMass (physicalScale attachment)
literalGapIsPhysicalRate attachment =
  sym
    (physicalRateIsLiteralGap attachment)

physicalRateIsSIMassMagnitude :
  ∀ {C S}
    {pinned : Pinned.PinnedYangMillsConstruction {C = C} S}
    {G : Top.CompactSimpleGroup C}
    (attachment : PinnedPhysicalClusteringAttachment pinned G) →
  Scale.physicalMass (physicalScale attachment)
  ≡
  SI.magnitude
    (SI.SIYangMillsMassGap.massGap
      (Pinned.pinnedSIMassGap pinned G))
physicalRateIsSIMassMagnitude
  {pinned = pinned} {G = G} attachment =
  trans
    (physicalRateIsLiteralGap attachment)
    (Pinned.pinnedLiteralGapIsSIMassMagnitude pinned G)

physicalRateIsSIEnergyMagnitude :
  ∀ {C S}
    {pinned : Pinned.PinnedYangMillsConstruction {C = C} S}
    {G : Top.CompactSimpleGroup C} →
  PinnedPhysicalClusteringAttachment pinned G →
  ℚ
physicalRateIsSIEnergyMagnitude {pinned = pinned} {G = G} attachment =
  SI.magnitude
    (SI.SIYangMillsMassGap.energyGap
      (Pinned.pinnedSIMassGap pinned G))

pinnedPhysicalClusteringAttachmentCompilerLevel : ProofLevel
pinnedPhysicalClusteringAttachmentCompilerLevel = machineChecked

pinnedSIPhysicalRateAttachmentCompilerLevel : ProofLevel
pinnedSIPhysicalRateAttachmentCompilerLevel = machineChecked

-- Actual source theorem still required:
-- cutoff-uniform physical-separation clustering at this positive rate.
pinnedUniformPhysicalClusteringInputLevel : ProofLevel
pinnedUniformPhysicalClusteringInputLevel = conditional
