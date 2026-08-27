module DASHI.Core.CriticalRelationalGrammarCapstoneExact where

------------------------------------------------------------------------
-- CRITICAL RELATIONAL GRAMMAR CAPSTONE
--
-- This module assembles the cross-pollinated theorem surfaces without claiming
-- a master critical-theory ontology.  Historical sources remain bounded in
-- CriticalRelationalGrammarSourceRegistryExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.RelationalRoleGrammarExact as Grammar
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.LacanFregeTernaryRoleChartExact as Lacan
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LacanIrigaray
import DASHI.Core.LacanS2RoleSeparationExact as LacanS2
import DASHI.Core.CriticalThirdnessRoleGrammarExact as Thirdness
import DASHI.Core.CriticalGrammarRelabellingBoundaryExact as Relabel
import DASHI.Core.IrigarayLabialRelationalCarrierExact as Irigaray
import DASHI.Core.LugonesPurityCurdlingNonfactorabilityExact as Lugones
import DASHI.Core.BadiouVoidCountAsOneBoundaryExact as Badiou
import DASHI.Core.SocialEcologyHierarchyProjectionBoundaryExact as Hierarchy
import DASHI.Core.CriticalSocialEcologyObserverRegimeExact as Ecology
import DASHI.Core.ZeroValueFibreNontrivialityExact as ZeroFibre

------------------------------------------------------------------------
-- Distinct uses of a zero-like address are explicitly tagged.
------------------------------------------------------------------------

data ZeroLikeRole : Set where
  lacanianInexistenceRole
  irigarayanNeitherRole
  anzalduanBorderRole
  bhabhaThirdSpaceRole
  badiouVoidRole
  coarseObserverZeroRole
  : ZeroLikeRole

lacanZero≠irigarayNeither :
  lacanianInexistenceRole ≡ irigarayanNeitherRole → ⊥
lacanZero≠irigarayNeither ()

irigarayNeither≠anzalduaBorder :
  irigarayanNeitherRole ≡ anzalduanBorderRole → ⊥
irigarayNeither≠anzalduaBorder ()

anzalduaBorder≠bhabhaThird :
  anzalduanBorderRole ≡ bhabhaThirdSpaceRole → ⊥
anzalduaBorder≠bhabhaThird ()

badiouVoid≠observerZero : badiouVoidRole ≡ coarseObserverZeroRole → ⊥
badiouVoid≠observerZero ()

------------------------------------------------------------------------
-- Carrier/grammar/semantics form three distinct comparison levels.
------------------------------------------------------------------------

lacanIrigarayNotRelatedByTernaryRelabelling :
  (permutation : Ternary.TernaryPermutation) →
  LacanIrigaray.GrammarPreserving permutation → ⊥
lacanIrigarayNotRelatedByTernaryRelabelling =
  LacanIrigaray.noTernaryRelabellingPreservesGrammar

anzalduaAndBhabhaSameCarrierDifferentGrammar :
  Grammar.GrammarDifferenceWitness
    Thirdness.anzalduaPluralEdge Thirdness.bhabhaGenerativeEdge
anzalduaAndBhabhaSameCarrierDifferentGrammar =
  Thirdness.anzaldua≠bhabhaGrammar

anzalduaBhabhaNotRelatedByTernaryRelabelling :
  (permutation : Ternary.TernaryPermutation) →
  Relabel.AnzalduaBhabhaPreserving permutation → ⊥
anzalduaBhabhaNotRelatedByTernaryRelabelling =
  Relabel.noAnzalduaBhabhaTernaryRelabelling

lacanBhabhaGraphsRelabelExactly :
  (left right : Ternary.TernaryRoleCode) →
  Lacan.lacanOneCentredEdge left right
  ≡ Thirdness.bhabhaGenerativeEdge
      (Ternary.permute Ternary.swap01Permutation left)
      (Ternary.permute Ternary.swap01Permutation right)
lacanBhabhaGraphsRelabelExactly = Relabel.lacanBhabhaSwap01

------------------------------------------------------------------------
-- Non-ternary theorem surfaces remain non-ternary.
------------------------------------------------------------------------

lugonesAntiPureFactorisation : Lugones.PureEndpointFactorisation → ⊥
lugonesAntiPureFactorisation =
  Lugones.curdledWitnessBlocksPureEndpointFactorisation

badiouCountSurfaceHasNontrivialFibre : Badiou.CountAsOneCollision
badiouCountSurfaceHasNontrivialFibre = Badiou.canonicalCountAsOneCollision

coarseZeroDoesNotDetermineFuture :
  INF.FactorsThrough ZeroFibre.zeroObserver ZeroFibre.futureClass → ⊥
coarseZeroDoesNotDetermineFuture =
  ZeroFibre.zeroObservationCannotRecoverFutureClass

inclusiveRhetoricDoesNotDetermineAccessibility :
  INF.FactorsThrough Ecology.feministObserver Ecology.realizedRemain → ⊥
inclusiveRhetoricDoesNotDetermineAccessibility =
  Ecology.inclusiveReadingCannotRecoverRealizedAffordance

------------------------------------------------------------------------
-- Boundary: this is a comparison atlas, not a synthesis into one theory.
------------------------------------------------------------------------

record CriticalRelationalGrammarBoundary : Set where
  constructor critical-relational-grammar-boundary
  field
    allZeroLikeRolesAreOneConcept : Bool
    allZeroLikeRolesAreOneConceptIsFalse :
      allZeroLikeRolesAreOneConcept ≡ false
    everyThirdnessTheoryUsesTernaryCarrierNatively : Bool
    everyThirdnessTheoryUsesTernaryCarrierNativelyIsFalse :
      everyThirdnessTheoryUsesTernaryCarrierNatively ≡ false
    badiouCountAsOneIsTernaryRole : Bool
    badiouCountAsOneIsTernaryRoleIsFalse :
      badiouCountAsOneIsTernaryRole ≡ false
    lugonesCurdlingIsThirdCode : Bool
    lugonesCurdlingIsThirdCodeIsFalse :
      lugonesCurdlingIsThirdCode ≡ false
    hierarchyFollowsNumericCarrierOrder : Bool
    hierarchyFollowsNumericCarrierOrderIsFalse :
      hierarchyFollowsNumericCarrierOrder ≡ false
    graphIsomorphismImpliesSemanticIdentity : Bool
    graphIsomorphismImpliesSemanticIdentityIsFalse :
      graphIsomorphismImpliesSemanticIdentity ≡ false
    socialObserverApprovalEqualsMaterialAffordance : Bool
    socialObserverApprovalEqualsMaterialAffordanceIsFalse :
      socialObserverApprovalEqualsMaterialAffordance ≡ false
    sharedFormalPatternImpliesSharedHistoricalDoctrine : Bool
    sharedFormalPatternImpliesSharedHistoricalDoctrineIsFalse :
      sharedFormalPatternImpliesSharedHistoricalDoctrine ≡ false

canonicalCriticalRelationalGrammarBoundary : CriticalRelationalGrammarBoundary
canonicalCriticalRelationalGrammarBoundary =
  critical-relational-grammar-boundary
    false refl false refl false refl false refl false refl false refl false refl false refl
