module DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DIRECT SOURCE LOCATOR
--
-- The abstract states that this paper concludes the R-operation bounds and
-- completes the ultraviolet-stability proof for four-dimensional pure gauge
-- field theories.  Theorem 1 in the Introduction states:
--
--   if the effective coupling constants stay in (0,gamma] for sufficiently
--   small gamma, then the effective densities p_k have the form and satisfy
--   all conditions and bounds described in Sect. 2 of the preceding complete-
--   density paper.
--
-- The paragraph immediately following Theorem 1 is essential: Bałaban says
-- the theorem that would remove the coupling-smallness assumption relies on a
-- long second-order perturbative calculation whose proof had not been
-- published.  We therefore import ONLY the conditional Theorem 1 and never
-- promote the history-dependent beta enclosure from this source.
--
-- DASHI CONTRIBUTION
--
-- Make the strongest verified source reuse explicit.  RG1b/RG1a/the combined
-- complete-density preservation need not be reinvented as unrelated generic
-- polymer estimates: the published theorem already supplies the joint
-- small-/large-field inductive preservation, conditional on (i) a literal
-- dictionary from Bałaban's Sect.-2 density class to the repository state and
-- (ii) the small effective-coupling hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Balaban1989EffectiveDensityFlow
    (Coupling Density : Set) : Set₁ where
  field
    couplingAt : Nat → Coupling
    densityAt : Nat → Density

    Positive : Coupling → Set
    LessEqual : Coupling → Coupling → Set
    gamma : Coupling

    InSection2DensityClass : Nat → Density → Set
    Section2ConditionsAndBounds : Nat → Density → Set

    allEffectiveCouplingsSmall : ∀ scale →
      Positive (couplingAt scale) →
      LessEqual (couplingAt scale) gamma

    allEffectiveCouplingsPositive : ∀ scale → Positive (couplingAt scale)

open Balaban1989EffectiveDensityFlow public

-- This is the literal theorem authority imported from Bałaban 1989.  It is a
-- source theorem rather than a DASHI-derived proof.  The consumer must still
-- exhibit the source/repository carrier dictionary.
record Balaban1989Theorem1Witness
    {Coupling Density : Set}
    (flow : Balaban1989EffectiveDensityFlow Coupling Density) : Set₁ where
  field
    effectiveDensitiesPreserveSection2Form : ∀ scale →
      InSection2DensityClass flow scale (densityAt flow scale)

    effectiveDensitiesSatisfySection2Bounds : ∀ scale →
      Section2ConditionsAndBounds flow scale (densityAt flow scale)

open Balaban1989Theorem1Witness public

------------------------------------------------------------------------
-- Exact source-to-DASHI dictionary boundary.
------------------------------------------------------------------------

record BalabanTheorem1ToRepositoryDictionary
    {Coupling Density RepositoryState : Set}
    (flow : Balaban1989EffectiveDensityFlow Coupling Density) : Set₁ where
  field
    stateAt : Nat → RepositoryState

    RepositoryAdmissible : RepositoryState → Set
    RepositorySmallLargeFieldClosed : RepositoryState → Set
    RepositoryPolymerNormClosed : RepositoryState → Set
    RepositoryBoundaryTermsAdmissible : RepositoryState → Set

    section2FormImpliesRepositoryAdmissible : ∀ scale →
      InSection2DensityClass flow scale (densityAt flow scale) →
      RepositoryAdmissible (stateAt scale)

    section2BoundsImplySmallLargeFieldClosure : ∀ scale →
      Section2ConditionsAndBounds flow scale (densityAt flow scale) →
      RepositorySmallLargeFieldClosed (stateAt scale)

    section2BoundsImplyPolymerClosure : ∀ scale →
      Section2ConditionsAndBounds flow scale (densityAt flow scale) →
      RepositoryPolymerNormClosed (stateAt scale)

    section2BoundsImplyBoundaryAdmissible : ∀ scale →
      Section2ConditionsAndBounds flow scale (densityAt flow scale) →
      RepositoryBoundaryTermsAdmissible (stateAt scale)

open BalabanTheorem1ToRepositoryDictionary public

record RepositoryTheorem1Consequences
    {Coupling Density RepositoryState : Set}
    {flow : Balaban1989EffectiveDensityFlow Coupling Density}
    (dictionary : BalabanTheorem1ToRepositoryDictionary flow)
    (source : Balaban1989Theorem1Witness flow)
    (scale : Nat) : Set where
  field
    admissible : RepositoryAdmissible dictionary (stateAt dictionary scale)
    smallLargeFieldClosed :
      RepositorySmallLargeFieldClosed dictionary (stateAt dictionary scale)
    polymerNormClosed :
      RepositoryPolymerNormClosed dictionary (stateAt dictionary scale)
    boundaryAdmissible :
      RepositoryBoundaryTermsAdmissible dictionary (stateAt dictionary scale)

open RepositoryTheorem1Consequences public

balabanTheorem1Transported :
  ∀ {Coupling Density RepositoryState}
    {flow : Balaban1989EffectiveDensityFlow Coupling Density}
    (dictionary : BalabanTheorem1ToRepositoryDictionary flow)
    (source : Balaban1989Theorem1Witness flow)
    scale →
  RepositoryTheorem1Consequences dictionary source scale
balabanTheorem1Transported dictionary source scale = record
  { admissible =
      section2FormImpliesRepositoryAdmissible dictionary scale
        (effectiveDensitiesPreserveSection2Form source scale)
  ; smallLargeFieldClosed =
      section2BoundsImplySmallLargeFieldClosure dictionary scale
        (effectiveDensitiesSatisfySection2Bounds source scale)
  ; polymerNormClosed =
      section2BoundsImplyPolymerClosure dictionary scale
        (effectiveDensitiesSatisfySection2Bounds source scale)
  ; boundaryAdmissible =
      section2BoundsImplyBoundaryAdmissible dictionary scale
        (effectiveDensitiesSatisfySection2Bounds source scale)
  }

balaban1989Theorem1SourceLevel : ProofLevel
balaban1989Theorem1SourceLevel = standardImported

balaban1989Theorem1RepositoryTransportLevel : ProofLevel
balaban1989Theorem1RepositoryTransportLevel = machineChecked

-- These are intentionally separate.  The published 1989 theorem supplies the
-- complete-density RG step only after its own small-coupling hypothesis.  The
-- exact carrier dictionary and the positive history-dependent beta enclosure
-- remain the two physical seams which cannot be obtained by citation alone.
balaban1989Section2RepositoryDictionaryLevel : ProofLevel
balaban1989Section2RepositoryDictionaryLevel = conditional

balaban1989SmallEffectiveCouplingFromBetaLevel : ProofLevel
balaban1989SmallEffectiveCouplingFromBetaLevel = conditional
