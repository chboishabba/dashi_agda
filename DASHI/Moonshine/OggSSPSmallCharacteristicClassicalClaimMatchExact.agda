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
  p3DeligneRapoportThreeStratumC2Set :
    SmallCharacteristicClaim
  p2UniqueGamma04SupersingularDrinfeldLevel :
    SmallCharacteristicClaim
  p2BinaryTetrahedralSevenConjugacyClasses :
    SmallCharacteristicClaim
  p2BinaryTetrahedralFiveInversionOrbits :
    SmallCharacteristicClaim
  p2TwoOrientedQuadraticOrders :
    SmallCharacteristicClaim
  p2OrientedInertiaTenStateFactorization :
    SmallCharacteristicClaim
  p3F9QuotientAsDeligneRapoportStratumCode :
    SmallCharacteristicClaim
  p2OrientedInertiaEnrichedModuliProblem :
    SmallCharacteristicClaim

data MatchGrade : Set where
  directSourceMatch :
    MatchGrade
  frameworkSourceMatch :
    MatchGrade
  repositoryOnly :
    MatchGrade
  classicalNoGo :
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

p3LocalStrataMatch : ClaimMatch
p3LocalStrataMatch =
  claim-match
    p3DeligneRapoportThreeStratumC2Set
    directSourceMatch
    "Deligne-Rapoport special fibre of X0(p)"
    "two bad-prime components meet at the supersingular point; Frobenius/Verschiebung branches with node-fixed duality give the exact abstract three-stratum C2-set used by DASHI at p=3"
    true
    true

p2UniqueGamma04LevelMatch : ClaimMatch
p2UniqueGamma04LevelMatch =
  claim-match
    p2UniqueGamma04SupersingularDrinfeldLevel
    directSourceMatch
    "Katz-Mazur / Bertolini-Darmon-Prasanna-Conrad"
    "a supersingular elliptic curve has a unique Drinfeld cyclic subgroup scheme of order p^r, ker(F^r); at p=2,r=2 this blocks interpreting the ten DASHI states as ten Gamma0(4) supersingular level structures"
    true
    false

p2SevenClassesMatch : ClaimMatch
p2SevenClassesMatch =
  claim-match
    p2BinaryTetrahedralSevenConjugacyClasses
    directSourceMatch
    "Dadhwal-Pankaj, Group codes over binary tetrahedral group"
    "the binary tetrahedral automorphism group has seven conjugacy classes"
    true
    false

p2FiveInversionOrbitMatch : ClaimMatch
p2FiveInversionOrbitMatch =
  claim-match
    p2BinaryTetrahedralFiveInversionOrbits
    repositoryOnly
    "DASHI reconstruction from the sourced seven-class table"
    "inversion fixes the identity, central-minus-one and order-four classes while pairing the two order-three and two order-six classes, yielding exactly five inversion-orbits"
    true
    false

p2TwoOrientationsMatch : ClaimMatch
p2TwoOrientationsMatch =
  claim-match
    p2TwoOrientedQuadraticOrders
    directSourceMatch
    "Goren-Love, On elements of prescribed norm in maximal orders of a quaternion algebra"
    "every imaginary quadratic discriminant has exactly two oriented orders up to oriented isomorphism, exchanged by nontrivial Galois"
    true
    false

p2TenFactorizationMatch : ClaimMatch
p2TenFactorizationMatch =
  claim-match
    p2OrientedInertiaTenStateFactorization
    repositoryOnly
    "DASHI cross-module construction from two classical factors"
    "two oriented quadratic-order sheets times five inversion-orbits of binary-tetrahedral inertia gives an exact ten-element carrier; the product is not attributed to either classical source as a named moduli object"
    true
    false

p3StratumCodeMatch : ClaimMatch
p3StratumCodeMatch =
  claim-match
    p3F9QuotientAsDeligneRapoportStratumCode
    repositoryOnly
    "DASHI finite-code interpretation over Deligne-Rapoport local geometry"
    "the three-valued F9 extension quotient is exactly recharted to Frobenius-branch/node/Verschiebung-branch incidence strata; it is a stratum classifier, not the completed-local-ring coordinate"
    true
    false

p2EnrichedModuliMatch : ClaimMatch
p2EnrichedModuliMatch =
  claim-match
    p2OrientedInertiaEnrichedModuliProblem
    repositoryOnly
    "DASHI enriched moduli problem assembled from classical orientation and inertia ingredients"
    "objects carry an oriented quadratic-order marking plus an automorphism class; loop reversal is quotiented at the sector level, giving exactly ten coarse sectors"
    true
    false

p3SameObjectMatch : ClaimMatch
p3SameObjectMatch =
  claim-match
    p3DASHICarrierEqualsClassicalMarkedModuliObject
    noClassicalSameObjectMatch
    "no classical same-object source claimed"
    "the abstract three-state C2-set is classically realized by Deligne-Rapoport local strata, but the F9 coordinate itself is a DASHI stratum code rather than a classically identified formal local parameter"
    false
    false

p2SameObjectMatch : ClaimMatch
p2SameObjectMatch =
  claim-match
    p2DASHICarrierEqualsClassicalX04MarkedModuliObject
    classicalNoGo
    "Katz-Mazur / Bertolini-Darmon-Prasanna-Conrad supersingular Drinfeld-level uniqueness"
    "the unique supersingular order-4 Drinfeld cyclic subgroup blocks a ten-component Gamma0(4) level-point interpretation; the DASHI ten-state carrier must live in richer orientation/inertia marking data instead"
    true
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
  ∷ p3LocalStrataMatch
  ∷ p2UniqueGamma04LevelMatch
  ∷ p2SevenClassesMatch
  ∷ p2FiveInversionOrbitMatch
  ∷ p2TwoOrientationsMatch
  ∷ p2TenFactorizationMatch
  ∷ p3StratumCodeMatch
  ∷ p2EnrichedModuliMatch
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
    p3AbstractThreeStateC2SetClassicallyRealized : Bool
    p2Gamma04TenPointInterpretationClassicallyRejected : Bool
    p2SevenInertiaClassesClassicallySourced : Bool
    p2FiveInversionOrbitCarrierConstructed : Bool
    p2TwoOrientationFactorClassicallySourced : Bool
    p2TenCarrierHasClassicallySourcedFactorization : Bool
    p2TenCarrierNamedClassicalModuliObjectIdentified : Bool
    p3StratumCodeInterpretationPaid : Bool
    p2SpecificEnrichedModuliProblemDefined : Bool
    allUnsupportedPromotionsExplicitlyBlocked : Bool

canonicalClassicalClaimMatchBoundary :
  ClassicalClaimMatchBoundary
canonicalClassicalClaimMatchBoundary =
  classical-claim-match-boundary
    true true true true true true
    false false false false
    true true true true true true false
    true true
    true
