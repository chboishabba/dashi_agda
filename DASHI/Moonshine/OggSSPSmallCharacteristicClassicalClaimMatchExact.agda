module DASHI.Moonshine.OggSSPSmallCharacteristicClassicalClaimMatchExact where

------------------------------------------------------------------------
-- CLAIM-BY-CLAIM CLASSICAL SOURCE MATCH
--
-- This is the theorem-attribution ledger for the p=2/p=3 lane.
-- It distinguishes:
--
--   direct theorem/source match,
--   framework-only support,
--   repository reconstruction,
--   no classical same-object source claimed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Atlas

data SmallCharacteristicClaim : Set where
  p2UniqueSupersingularCoarseClass :
    SmallCharacteristicClaim
  p3UniqueSupersingularCoarseClass :
    SmallCharacteristicClaim
  p2ExceptionalAutomorphismEnhancement :
    SmallCharacteristicClaim
  p3ExceptionalAutomorphismEnhancement :
    SmallCharacteristicClaim
  cmNonSplitReductionIsSupersingular :
    SmallCharacteristicClaim
  cmReductionCarriesNormalizedOptimalEmbedding :
    SmallCharacteristicClaim
  badPrimeLevelNeedsDrinfeldGroupSchemeStructure :
    SmallCharacteristicClaim
  gamma0PrimePowerNeedsStackAwareIntegralModuli :
    SmallCharacteristicClaim
  p3ExactThreeStateDASHICarrier :
    SmallCharacteristicClaim
  p2ExactTenStateDASHICarrier :
    SmallCharacteristicClaim
  p3DASHICarrierEqualsClassicalMarkedModuliObject :
    SmallCharacteristicClaim
  p2DASHICarrierEqualsClassicalX04MarkedModuliObject :
    SmallCharacteristicClaim

data MatchGrade : Set where
  directSourceMatch :
    MatchGrade
  frameworkSourceMatch :
    MatchGrade
  repositoryOnly :
    MatchGrade
  noClassicalSameObjectMatch :
    MatchGrade

record ClaimMatch : Set where
  constructor claim-match
  field
    claim :
      SmallCharacteristicClaim
    grade :
      MatchGrade
    sourceLabel :
      String
    relationship :
      String
    classicalAuthorityUsed :
      Bool
    exactDASHISameObjectClaimLicensed :
      Bool

open ClaimMatch public

p2UniqueCoarseMatch : ClaimMatch
p2UniqueCoarseMatch =
  claim-match
    p2UniqueSupersingularCoarseClass
    directSourceMatch
    "Silverman, The Arithmetic of Elliptic Curves, V.4"
    "direct classical classification: over the algebraic closure of F2 there is one supersingular elliptic curve, y^2+y=x^3, hence one coarse supersingular j-class"
    true
    false

p3UniqueCoarseMatch : ClaimMatch
p3UniqueCoarseMatch =
  claim-match
    p3UniqueSupersingularCoarseClass
    directSourceMatch
    "Silverman, The Arithmetic of Elliptic Curves, V.4"
    "direct Hasse-polynomial classification: H_3(t)=1+t gives exactly one supersingular Legendre isomorphism class; j=0=1728 in characteristic 3"
    true
    false

p2AutomorphismMatch : ClaimMatch
p2AutomorphismMatch =
  claim-match
    p2ExceptionalAutomorphismEnhancement
    directSourceMatch
    "Silverman, The Arithmetic of Elliptic Curves, III.10 / Appendix A"
    "classical exceptional characteristic-2 automorphism group has order 24 at j=0=1728"
    true
    false

p3AutomorphismMatch : ClaimMatch
p3AutomorphismMatch =
  claim-match
    p3ExceptionalAutomorphismEnhancement
    directSourceMatch
    "Silverman, The Arithmetic of Elliptic Curves, III.10 / Appendix A"
    "classical exceptional characteristic-3 automorphism group has order 12 at j=0=1728"
    true
    false

deuringReductionMatch : ClaimMatch
deuringReductionMatch =
  claim-match
    cmNonSplitReductionIsSupersingular
    directSourceMatch
    "Deuring reduction theorem as used explicitly by Elkies-Ono-Yang (2005)"
    "if the CM prime is inert or ramified, good reduction is supersingular"
    true
    false

optimalEmbeddingMatch : ClaimMatch
optimalEmbeddingMatch =
  claim-match
    cmReductionCarriesNormalizedOptimalEmbedding
    directSourceMatch
    "Elkies-Ono-Yang, Reduction of CM elliptic curves and modular function congruences"
    "a normalized CM action reduces to a normalized optimal embedding of the CM order into the supersingular endomorphism ring; this is genuine marking beyond coarse j"
    true
    false

drinfeldLevelMatch : ClaimMatch
drinfeldLevelMatch =
  claim-match
    badPrimeLevelNeedsDrinfeldGroupSchemeStructure
    directSourceMatch
    "Katz-Mazur, Arithmetic Moduli of Elliptic Curves"
    "p-power level in characteristic p is formulated by Drinfeld level structures/group schemes rather than a naive set of ordinary torsion points"
    true
    false

gamma0StackMatch : ClaimMatch
gamma0StackMatch =
  claim-match
    gamma0PrimePowerNeedsStackAwareIntegralModuli
    directSourceMatch
    "Conrad, Arithmetic moduli of generalized elliptic curves"
    "for non-squarefree p-power level, Γ0(n) moduli in bad characteristic can have non-etale automorphisms and naturally require Artin-stack/integral moduli semantics"
    true
    false

p3ThreeStateMatch : ClaimMatch
p3ThreeStateMatch =
  claim-match
    p3ExactThreeStateDASHICarrier
    repositoryOnly
    "DASHI formal reconstruction"
    "the pointed three-state carrier {unmarked/zero, two exchanged nonzero markings} is an internal finite presentation of the reconstructed F9 extension-coordinate quotient"
    false
    false

p2TenStateMatch : ClaimMatch
p2TenStateMatch =
  claim-match
    p2ExactTenStateDASHICarrier
    repositoryOnly
    "DASHI formal reconstruction"
    "the ten-state CMOrientation x NineOrbit carrier is a repository presentation chosen to retain orientation and five inner orbit labels"
    false
    false

p3SameObjectMatch : ClaimMatch
p3SameObjectMatch =
  claim-match
    p3DASHICarrierEqualsClassicalMarkedModuliObject
    noClassicalSameObjectMatch
    "no classical same-object source claimed"
    "classical sources support supersingular CM marking and Frobenius action, but do not identify the exact DASHI three-state quotient as a named classical moduli problem"
    false
    false

p2SameObjectMatch : ClaimMatch
p2SameObjectMatch =
  claim-match
    p2DASHICarrierEqualsClassicalX04MarkedModuliObject
    noClassicalSameObjectMatch
    "no classical same-object source claimed"
    "Katz-Mazur/Conrad support bad-characteristic level-4 group-scheme moduli, but do not identify the DASHI ten-state discrete carrier with the geometric points or groupoid of X0(4) in characteristic 2"
    false
    false

canonicalClaimMatches : List ClaimMatch
canonicalClaimMatches =
  p2UniqueCoarseMatch
  ∷ p3UniqueCoarseMatch
  ∷ p2AutomorphismMatch
  ∷ p3AutomorphismMatch
  ∷ deuringReductionMatch
  ∷ optimalEmbeddingMatch
  ∷ drinfeldLevelMatch
  ∷ gamma0StackMatch
  ∷ p3ThreeStateMatch
  ∷ p2TenStateMatch
  ∷ p3SameObjectMatch
  ∷ p2SameObjectMatch
  ∷ []

data CitationUpgradesRepositoryCarrierToClassicalSameObject : Set where
data ClassicalMarkedFrameworkDeterminesFiniteCardinality : Set where

citationDoesNotUpgradeRepositoryCarrier :
  CitationUpgradesRepositoryCarrierToClassicalSameObject -> ⊥
citationDoesNotUpgradeRepositoryCarrier ()

markedFrameworkDoesNotDetermineFiniteCardinality :
  ClassicalMarkedFrameworkDeterminesFiniteCardinality -> ⊥
markedFrameworkDoesNotDetermineFiniteCardinality ()

record ClassicalClaimMatchBoundary : Set where
  constructor classical-claim-match-boundary
  field
    coarseP2DirectlySourced : Bool
    coarseP3DirectlySourced : Bool
    smallCharacteristicAutomorphismsDirectlySourced : Bool
    deuringReductionDirectlySourced : Bool
    optimalEmbeddingMarkingDirectlySourced : Bool
    badPrimeLevelModuliDirectlySourced : Bool
    exactThreeStatePresentationClassical : Bool
    exactTenStatePresentationClassical : Bool
    p3SameObjectClassicallyIdentified : Bool
    p2SameObjectClassicallyIdentified : Bool
    allUnsupportedPromotionsExplicitlyBlocked : Bool

canonicalClassicalClaimMatchBoundary :
  ClassicalClaimMatchBoundary
canonicalClassicalClaimMatchBoundary =
  classical-claim-match-boundary
    true true true true true true
    false false false false true
