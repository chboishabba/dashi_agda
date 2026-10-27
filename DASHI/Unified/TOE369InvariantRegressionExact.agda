module DASHI.Unified.TOE369InvariantRegressionExact where

------------------------------------------------------------------------
-- TOE 369 INVARIANT REGRESSION
--
-- This module does not add a new theory.
-- It pins existing exact results at the TOE boundary.
--
-- Legal/governance invariants:
--   heuristic evidence does not promote authority;
--   crawling stays closed;
--   partial claim coverage is not whole-claim support.
--
-- Arithmetic/moonshine invariants:
--   the arithmetic/moonshine facade stays non-promoting;
--   the actual F4 curve shear has order three;
--   Frobenius conjugates the shear to its inverse.
--
-- These statements coexist.
-- They do not imply a legal claim, a Monster valuation, or Gamma0(4).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Unified.TOELegalGovernanceHandoffExact as Legal
import DASHI.Unified.ArithmeticMoonshine as Arithmetic
import DASHI.Unified.InvariantSpine as Spine
import DASHI.Moonshine.OggSSPP2F4CurveShearReflectionExact as CurveS3
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve

legalAuthorityRemainsClosed :
  Legal.Authority.promotesAnyAuthority
    Legal.Semantic.semanticPromotionAuthorityBoundary
  ≡ false
legalAuthorityRemainsClosed =
  Legal.toeLegalGovernancePostcondition

legalNetworkCrawlingRemainsClosed :
  Legal.Network.GovernedLegalNetworkBoundary.crawlingPermitted
    (Legal.networkBoundary Legal.canonicalZKPTOELegalGovernanceHandoff)
  ≡ false
legalNetworkCrawlingRemainsClosed =
  Legal.toeLegalGovernanceNetworkPostcondition

partialClaimCoverageRemainsNonTerminal :
  Legal.Audit.ClaimAuditManifestBoundary.partialObligationCoverageEqualsWholeClaimSupport
    (Legal.claimAuditBoundary Legal.canonicalZKPTOELegalGovernanceHandoff)
  ≡ false
partialClaimCoverageRemainsNonTerminal =
  Legal.toeLegalGovernanceAuditPostcondition

arithmeticMoonshineExternalPromotionRemainsClosed :
  Spine.objectExternalJPromotion Arithmetic.arithmeticMoonshineObject
  ≡ false
arithmeticMoonshineExternalPromotionRemainsClosed =
  Arithmetic.arithmeticMoonshineJPromotionBlocked

f4CurveShearOrderThree :
  (p : Curve.RationalF4Point) →
  CurveS3.rho (CurveS3.rhoTwice p) ≡ p
f4CurveShearOrderThree =
  CurveS3.rhoThree

f4FrobeniusConjugatesShearToInverse :
  (p : Curve.RationalF4Point) →
  CurveS3.frobenius
    (CurveS3.rho (CurveS3.frobenius p))
  ≡ CurveS3.rhoTwice p
f4FrobeniusConjugatesShearToInverse =
  CurveS3.frobeniusConjugatesRho
