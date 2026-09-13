module DASHI.Wikimedia.IbrahimDeltaRedirectWeierstrassEllipticLatticeSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimDedekindEtaDeltaJNonvanishingSnowballExact as EtaDelta
import DASHI.Wikimedia.IbrahimAutomorphicHarmonicFourierSnowballExact as FourierWalk
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as JFricke
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein

------------------------------------------------------------------------
-- MODULAR-DISCRIMINANT REDIRECT -> WEIERSTRASS ELLIPTIC/LATTICE SNOWBALL
--
-- Current EN inspection 2026-09-10:
--   /wiki/Modular_discriminant redirects to Weierstrass elliptic function.
--   Weierstrass elliptic function -> Mathematics is its current first-body
--   link.  Its lead/body then exposes elliptic function, meromorphic function,
--   elliptic curve, period lattice, upper half-plane, Eisenstein series,
--   g2/g3 and the non-singular discriminant condition g2^3-27 g3^2 != 0.
--
-- External identities retained:
--   Weierstrass elliptic functions Q2343600
--   elliptic function             Q938102
--   meromorphic function          Q217616
--   elliptic curve                Q268493
--   Eisenstein series             Q1313257
--
-- The redirect and each later body relation are typed separately.  None is
-- promoted into an Ibrahim-2014 edge or DASHI theorem dependency.
------------------------------------------------------------------------

weierstrassEllipticQid : Identity.ExternalIdentityDemand
weierstrassEllipticQid = Identity.mkOptionalIdentityDemand
  "Delta redirect / Weierstrass snowball"
  "Weierstrass elliptic functions identity"
  "Weierstrass elliptic functions"
  Identity.wikidataQid
  (Identity.verified "Q2343600" "Wikidata oldid 2396905348 inspected 2026-09-10")

ellipticFunctionQid : Identity.ExternalIdentityDemand
ellipticFunctionQid = Identity.mkOptionalIdentityDemand
  "Weierstrass snowball" "elliptic-function identity" "elliptic function"
  Identity.wikidataQid
  (Identity.verified "Q938102" "Wikidata oldid 2436258924 inspected 2026-09-10")

meromorphicFunctionQid : Identity.ExternalIdentityDemand
meromorphicFunctionQid = EtaDelta.meromorphicFunctionQid

ellipticCurveQid : Identity.ExternalIdentityDemand
ellipticCurveQid = Identity.mkOptionalIdentityDemand
  "Weierstrass snowball" "elliptic-curve identity" "elliptic curve"
  Identity.wikidataQid
  (Identity.verified "Q268493" "Wikidata oldid 2486183434 inspected 2026-09-10")

eisensteinSeriesQid : Identity.ExternalIdentityDemand
eisensteinSeriesQid = Identity.mkOptionalIdentityDemand
  "Weierstrass snowball" "Eisenstein-series identity" "Eisenstein series"
  Identity.wikidataQid
  (Identity.verified "Q1313257" "Wikidata oldid 2489947618 inspected 2026-09-10")

weierstrassWikipediaRevision : Identity.ExternalIdentityDemand
weierstrassWikipediaRevision = Identity.mkOptionalIdentityDemand
  "Weierstrass snowball"
  "exact current Wikipedia revision"
  "Weierstrass elliptic function"
  Identity.wikimediaReferenceUrl
  (Identity.unresolved "current page inspected 2026-09-10 through Modular_discriminant redirect; exact permanent revision not retained in this tranche")

------------------------------------------------------------------------
-- Typed navigation/definition graph.
------------------------------------------------------------------------

data EdgeRole : Set where
  redirectEdge currentFirstBody secondaryDefinition secondaryProperty
  sourceFormula repositoryConstruction : EdgeRole

record TypedEdge : Set where
  constructor typed-edge
  field
    source : String
    target : String
    role : EdgeRole
    evidence : String
    createsFormalDependency : Bool
open TypedEdge public

deltaRedirectToWeierstrass : TypedEdge
deltaRedirectToWeierstrass = typed-edge
  "English Modular discriminant sitelink/Q56296629"
  "Weierstrass elliptic function/Q2343600"
  redirectEdge
  "Current English /wiki/Modular_discriminant resolves to the Weierstrass elliptic function article"
  false

weierstrassToMathematics : TypedEdge
weierstrassToMathematics = typed-edge
  "Weierstrass elliptic function/Q2343600"
  "Mathematics/Q395"
  currentFirstBody
  "Current EN body begins 'In mathematics'; Mathematics is the first main-body hyperlink"
  false

weierstrassToEllipticFunction : TypedEdge
weierstrassToEllipticFunction = typed-edge
  "Weierstrass elliptic function/Q2343600"
  "elliptic function/Q938102"
  secondaryDefinition
  "Wikidata subclasses Q2343600 under elliptic function; current EN lead says Weierstrass functions are elliptic functions"
  false

ellipticFunctionToMeromorphic : TypedEdge
ellipticFunctionToMeromorphic = typed-edge
  "elliptic function/Q938102"
  "meromorphic function/Q217616"
  secondaryDefinition
  "Wikidata Q938102 subclasses elliptic function under meromorphic and periodic function"
  false

weierstrassToEllipticCurve : TypedEdge
weierstrassToEllipticCurve = typed-edge
  "Weierstrass elliptic function/Q2343600"
  "elliptic curve/Q268493"
  secondaryDefinition
  "Current EN says wp together with its derivative parameterizes elliptic curves"
  false

weierstrassToEisenstein : TypedEdge
weierstrassToEisenstein = typed-edge
  "Weierstrass elliptic function/Q2343600"
  "Eisenstein series/Q1313257"
  secondaryDefinition
  "Current EN Laurent expansion expresses wp using G_n Eisenstein series and then g2=60G4, g3=140G6"
  false

periodLatticeToRepoLattice : TypedEdge
periodLatticeToRepoLattice = typed-edge
  "period lattice Lambda=Z omega1 + Z omega2"
  "DASHI Eisenstein LatticePoint/SL2Z reindexing"
  repositoryConstruction
  "Repo's Eisenstein theorem uses an explicit Z^2 lattice-index bijection; this is a structural reuse seam, not identity with every analytic period lattice"
  false

ellipticCurveToRepoJFricke : TypedEdge
ellipticCurveToRepoJFricke = typed-edge
  "elliptic curve/Q268493"
  "DASHI ModularJFrickeSystem.EllipticCurve"
  repositoryConstruction
  "Repo has an abstract elliptic-curve/J/Fricke interface; it intentionally does not manufacture literal elliptic curves"
  false

------------------------------------------------------------------------
-- Same-object / residual reading.
------------------------------------------------------------------------

record WeierstrassRepoCoverage : Set where
  constructor weierstrass-repo-coverage
  field
    externalWeierstrassIdentityPaid : Bool
    ellipticFunctionIdentityPaid : Bool
    ellipticCurveIdentityPaid : Bool
    eisensteinIdentityPaid : Bool
    repoIntegerLatticeReindexingPaid : Bool
    repoEisensteinTransformationPaid : Bool
    repoAbstractEllipticCurveJInterfacePaid : Bool
    literalPeriodLatticeComplexModelPaid : Bool
    literalEllipticCurveConstructionPaid : Bool
    discriminantNonvanishingFromNonsingularityPaid : Bool
    nextResidual : String
open WeierstrassRepoCoverage public

canonicalWeierstrassRepoCoverage : WeierstrassRepoCoverage
canonicalWeierstrassRepoCoverage = weierstrass-repo-coverage
  true true true true true true true false false false
  "build or import the concrete complex period-lattice/elliptic-curve model needed to turn the existing abstract lattice and J/Fricke interfaces into the same analytic object; keep g2^3-27g3^2 != 0 as an admissibility hypothesis until its domain proof is paid"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RedirectMeansSameWikidataItem : Set where
data PeriodLatticeEqualsNSZ3 : Set where
data AbstractEllipticCurveInterfaceConstructsCurve : Set where
data SharedEisensteinNameCreatesSameSeries : Set where
data DiscriminantConditionAutomaticallyProvesEtaNonzero : Set where

redirectDoesNotMergeItems : RedirectMeansSameWikidataItem → ⊥
redirectDoesNotMergeItems ()

periodLatticeIsNotNSZ3 : PeriodLatticeEqualsNSZ3 → ⊥
periodLatticeIsNotNSZ3 ()

interfaceDoesNotConstructCurve : AbstractEllipticCurveInterfaceConstructsCurve → ⊥
interfaceDoesNotConstructCurve ()

nameDoesNotCreateSameSeries : SharedEisensteinNameCreatesSameSeries → ⊥
nameDoesNotCreateSameSeries ()

discriminantHypothesisDoesNotPayEtaNonzero : DiscriminantConditionAutomaticallyProvesEtaNonzero → ⊥
discriminantHypothesisDoesNotPayEtaNonzero ()

etaDeltaBoundary : EtaDelta.EtaDeltaJSnowballBoundary
etaDeltaBoundary = EtaDelta.canonicalEtaDeltaJSnowballBoundary

fourierBoundary : FourierWalk.HarmonicFourierCoverage
fourierBoundary = FourierWalk.canonicalHarmonicFourierCoverage

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
