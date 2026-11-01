module DASHI.Physics.YangMills.BalabanSourceNativePublishedFlowEntryExact where

------------------------------------------------------------------------
-- ROUND76: LITERAL SOURCE-NATIVE STATE IS ACTUALLY IN THE PUBLISHED FLOW
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- CMP122 Theorem 1 says that, under its small-effective-coupling hypothesis,
-- the effective densities p_k retain the complete CMP119 Section-2 form and
-- bounds.  The repository already imports that theorem as
-- `Balaban1989Theorem1Witness`.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- This file closes the stronger version of the old source-entry seam.  It does
-- not merely say that two records have equal-looking fields.  A source-native
-- strong state is indexed by a scale of the ACTUAL imported Bałaban flow; its
-- CMP119 complete density is proved equal to `densityAt flow scale`.  We then
-- transport CMP122 Theorem-1 membership/bounds across that equality.  Hence
-- the strong state is literally a member of the published inductive class.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Published
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119
import DASHI.Physics.YangMills.BalabanSourceNativeStrongStateEntryExact as Native

record SourceNativePublishedFlow : Set₂ where
  field
    Coupling Density Operation Action Field : Set
    RegularTerm RTerm BoundaryTerm VacuumTerm : Set
    SmallFieldScale BlockRadius AnalyticRadius Decay : Set

    flow : Published.Balaban1989EffectiveDensityFlow Coupling Density
    theorem1 : Published.Balaban1989Theorem1Witness flow

    completeDensityAt : Nat →
      CMP119.CMP119Section2CompleteDensity
        Coupling Density Operation Action Field
        RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay

    densityIsFlowDensity : ∀ scale →
      CMP119.rho (completeDensityAt scale)
      ≡ Published.densityAt flow scale

    couplingIsFlowCoupling : ∀ scale →
      CMP119.g (completeDensityAt scale)
      ≡ Published.couplingAt flow scale

    differentiatedAt : Nat → Native.CMP109DifferentiatedCoordinate RegularTerm

open SourceNativePublishedFlow public

baselineAt :
  (published : SourceNativePublishedFlow) → Nat →
  Native.SourceNativeBalabanBaseline
baselineAt published scale = record
  { Native.SourceNativeBalabanBaseline.Coupling = Coupling published
  ; Native.SourceNativeBalabanBaseline.Density = Density published
  ; Native.SourceNativeBalabanBaseline.Operation = Operation published
  ; Native.SourceNativeBalabanBaseline.Action = Action published
  ; Native.SourceNativeBalabanBaseline.Field = Field published
  ; Native.SourceNativeBalabanBaseline.RegularTerm = RegularTerm published
  ; Native.SourceNativeBalabanBaseline.RTerm = RTerm published
  ; Native.SourceNativeBalabanBaseline.BoundaryTerm = BoundaryTerm published
  ; Native.SourceNativeBalabanBaseline.VacuumTerm = VacuumTerm published
  ; Native.SourceNativeBalabanBaseline.SmallFieldScale = SmallFieldScale published
  ; Native.SourceNativeBalabanBaseline.BlockRadius = BlockRadius published
  ; Native.SourceNativeBalabanBaseline.AnalyticRadius = AnalyticRadius published
  ; Native.SourceNativeBalabanBaseline.Decay = Decay published
  ; Native.SourceNativeBalabanBaseline.completeDensity = completeDensityAt published scale
  ; Native.SourceNativeBalabanBaseline.differentiated = differentiatedAt published scale
  }

record SourceNativeStrongStateAt
    (published : SourceNativePublishedFlow) (scale : Nat) : Set₂ where
  field
    strongState : Native.SourceNativeUnifiedState (baselineAt published scale)

open SourceNativeStrongStateAt public

record PublishedSection2Membership
    (published : SourceNativePublishedFlow) (scale : Nat) : Set₁ where
  field
    sourceForm :
      Published.InSection2DensityClass (flow published) scale
        (CMP119.rho (completeDensityAt published scale))
    sourceBounds :
      Published.Section2ConditionsAndBounds (flow published) scale
        (CMP119.rho (completeDensityAt published scale))

open PublishedSection2Membership public

sourceNativeStateIsInPublishedSection2Class :
  (published : SourceNativePublishedFlow) →
  ∀ scale → PublishedSection2Membership published scale
sourceNativeStateIsInPublishedSection2Class published scale = record
  { sourceForm =
      subst
        (λ density →
          Published.InSection2DensityClass (flow published) scale density)
        (sym (densityIsFlowDensity published scale))
        (Published.effectiveDensitiesPreserveSection2Form
          (theorem1 published) scale)
  ; sourceBounds =
      subst
        (λ density →
          Published.Section2ConditionsAndBounds (flow published) scale density)
        (sym (densityIsFlowDensity published scale))
        (Published.effectiveDensitiesSatisfySection2Bounds
          (theorem1 published) scale)
  }

record LiteralStateEntersPublishedBalabanRG
    (published : SourceNativePublishedFlow)
    (scale : Nat)
    (state : SourceNativeStrongStateAt published scale) : Set₂ where
  field
    sameObjectEntry :
      Native.LiteralPublishedBalabanEntry (strongState state)
    publishedMembership : PublishedSection2Membership published scale

open LiteralStateEntersPublishedBalabanRG public

literalStateEntersPublishedBalabanRG :
  (published : SourceNativePublishedFlow) →
  ∀ scale (state : SourceNativeStrongStateAt published scale) →
  LiteralStateEntersPublishedBalabanRG published scale state
literalStateEntersPublishedBalabanRG published scale state = record
  { sameObjectEntry = Native.literalStateEntersPublishedBalabanRG (strongState state)
  ; publishedMembership = sourceNativeStateIsInPublishedSection2Class published scale
  }

sourceNativePublishedFlowMembershipLevel : ProofLevel
sourceNativePublishedFlowMembershipLevel = machineChecked

-- The only source theorem assumption retained here is the one Bałaban actually
-- published: the effective-coupling-smallness hypothesis already bundled in
-- `flow`.  Obtaining that hypothesis from the literal Wilson/FP/Haar beta
-- theorem remains job #2, not a hidden premise of this source-entry compiler.
