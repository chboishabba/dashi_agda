module DASHI.Physics.YangMills.Balaban1989CompleteDensityToCombinedRGExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories - II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Relationship: this is the direct cluster-expansion sequel to CMP109; it
-- proves that the fluctuation-field cluster expansion preserves the inductive
-- assumptions in the small-field approximation.  It is an intermediate
-- source bridge, not a replacement for the later complete-density theorem.
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
-- DASHI CONTRIBUTION
--
-- Make the complete-density -> repository-state dictionary concrete at the
-- existing CombinedRGAdmissibility carrier.  The source theorem supplies, at
-- each scale, its Sect.-2 density form and bounds.  A literal dictionary must
-- identify those source conclusions with exactly the three predicates already
-- used by the repository invariant region: coupling, boundary and polymer norm
-- admissibility.  Once those identifications are supplied, the resulting
-- AdmissibleRGState is assembled without reproving the cluster/R-operation
-- estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV

record CompleteDensityCombinedRGDictionary
    {Coupling Density State Bound : Set}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    {normData : UV.CombinedOneStepPolymerNormData State Bound}
    (admissibility : UV.CombinedRGAdmissibility normData) : Set₁ where
  field
    sourceState : Nat → State

    sourceStateIsRepositoryTrajectory : ∀ scale →
      sourceState scale
      ≡ UV.stateAt normData (sourceState 0) scale

    sourceFormGivesCoupling : ∀ scale →
      Source.InSection2DensityClass flow scale
        (Source.densityAt flow scale) →
      UV.AdmissibleCoupling admissibility (sourceState scale)

    sourceBoundsGiveBoundary : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale
        (Source.densityAt flow scale) →
      UV.BoundaryAdmissible admissibility (sourceState scale)

    sourceBoundsGivePolymerNorm : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale
        (Source.densityAt flow scale) →
      UV.PolymerNormAdmissible admissibility (sourceState scale)

open CompleteDensityCombinedRGDictionary public

sourceTheoremGivesRepositoryAdmissibleState :
  ∀ {Coupling Density State Bound}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    {normData : UV.CombinedOneStepPolymerNormData State Bound}
    {admissibility : UV.CombinedRGAdmissibility normData}
    (dictionary : CompleteDensityCombinedRGDictionary admissibility)
    (theorem1 : Source.Balaban1989Theorem1Witness flow)
    scale →
  UV.AdmissibleRGState admissibility
    (UV.stateAt normData (sourceState dictionary 0) scale)
sourceTheoremGivesRepositoryAdmissibleState
    {admissibility = admissibility} dictionary theorem1 scale =
  let
    mapped : UV.AdmissibleRGState admissibility (sourceState dictionary scale)
    mapped = record
      { UV.AdmissibleRGState.couplingAdmissible =
          sourceFormGivesCoupling dictionary scale
            (Source.effectiveDensitiesPreserveSection2Form theorem1 scale)
      ; UV.AdmissibleRGState.boundaryAdmissible =
          sourceBoundsGiveBoundary dictionary scale
            (Source.effectiveDensitiesSatisfySection2Bounds theorem1 scale)
      ; UV.AdmissibleRGState.polymerNormAdmissible =
          sourceBoundsGivePolymerNorm dictionary scale
            (Source.effectiveDensitiesSatisfySection2Bounds theorem1 scale)
      }
  in
  subst
    (UV.AdmissibleRGState admissibility)
    (sourceStateIsRepositoryTrajectory dictionary scale)
    mapped

balabanCompleteDensityCombinedRGTransportLevel : ProofLevel
balabanCompleteDensityCombinedRGTransportLevel = machineChecked

-- This is now the single source-dictionary producer replacing separate generic
-- RG1a/RG1b reproofs.  It must identify Bałaban's actual Sect.-2 density class,
-- R-operation/boundary terms and polymer weights with these existing predicates.
balabanCompleteDensityCombinedRGDictionaryLevel : ProofLevel
balabanCompleteDensityCombinedRGDictionaryLevel = conditional
