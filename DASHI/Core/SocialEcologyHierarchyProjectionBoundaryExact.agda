module DASHI.Core.SocialEcologyHierarchyProjectionBoundaryExact where

------------------------------------------------------------------------
-- SOCIAL ECOLOGY / HIERARCHY PROJECTION BOUNDARY
--
-- SOURCE CONTEXT
--
-- Murray Bookchin, The Ecology of Freedom: The Emergence and Dissolution of
-- Hierarchy, original 1982; AK Press edition 2005, ISBN 9781904859260.
-- Ynestra King, "Healing the Wounds: Feminism, Ecology, and the Nature/Culture
-- Dualism", in Alison M. Jaggar & Susan Bordo (eds.), Gender/Body/Knowledge,
-- Rutgers University Press, 1989, ISBN 9780813513799. No chapter DOI asserted.
--
-- These sources motivate treating hierarchy/domination as relational/social-
-- ecological constructions rather than reading rank directly from a numerical
-- carrier.  The exact finite counterexample below is a DASHI theorem pattern.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.DifferenceWithoutHierarchyExact as Difference

------------------------------------------------------------------------
-- Same ternary carrier, two independently supplied normative regimes.
------------------------------------------------------------------------

rankedRegime :
  Ternary.TernaryRoleCode → Ternary.TernaryRoleCode → Bool
rankedRegime Ternary.code2 Ternary.code1 = true
rankedRegime Ternary.code1 Ternary.code0 = true
rankedRegime Ternary.code2 Ternary.code0 = true
rankedRegime _ _ = false

nonrankingRegime :
  Ternary.TernaryRoleCode → Ternary.TernaryRoleCode → Bool
nonrankingRegime _ _ = false

sameCarrierDifferentRanking :
  rankedRegime Ternary.code2 Ternary.code1
  ≡ nonrankingRegime Ternary.code2 Ternary.code1 → ⊥
sameCarrierDifferentRanking ()

------------------------------------------------------------------------
-- Difference without hierarchy remains live as the generic positive owner.
------------------------------------------------------------------------

differenceWithoutRankWitness :
  Difference.DifferenceWithEqualStanding
    Difference.modeObserver Difference.modeStanding
differenceWithoutRankWitness =
  Difference.canonicalDifferenceWithEqualStanding

record SocialEcologyHierarchyBoundary : Set where
  constructor social-ecology-hierarchy-boundary
  field
    ternaryCodeOrderDeterminesSocialRank : Bool
    ternaryCodeOrderDeterminesSocialRankIsFalse :
      ternaryCodeOrderDeterminesSocialRank ≡ false
    ecologicalDifferenceImpliesHierarchy : Bool
    ecologicalDifferenceImpliesHierarchyIsFalse :
      ecologicalDifferenceImpliesHierarchy ≡ false
    hierarchyIsNaturalPropertyOfCarrier : Bool
    hierarchyIsNaturalPropertyOfCarrierIsFalse :
      hierarchyIsNaturalPropertyOfCarrier ≡ false
    sourceCritiqueProvesNoHierarchyExistsEmpirically : Bool
    sourceCritiqueProvesNoHierarchyExistsEmpiricallyIsFalse :
      sourceCritiqueProvesNoHierarchyExistsEmpirically ≡ false

canonicalSocialEcologyHierarchyBoundary : SocialEcologyHierarchyBoundary
canonicalSocialEcologyHierarchyBoundary =
  social-ecology-hierarchy-boundary false refl false refl false refl false refl
