module DASHI.Analysis.DeBruijnNewmanRiemannG2BridgeAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as DBN
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as G2
import DASHI.Analysis.DeBruijnNewmanRiemannG2RiemannSiegelBridgeExact as RS
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- SOURCE-EXACT DBN -> RH G2 BRIDGE AUDIT
--
-- Published source (only for the DBN statements below):
--   D. H. J. Polymath,
--   "Effective approximation of heat flow evolution of the Riemann xi
--   function, and a new upper bound for the de Bruijn-Newman constant",
--   Research in the Mathematical Sciences 6 (2019),
--   DOI 10.1007/s40687-019-0193-1, arXiv:1904.12438.
--
-- Theorem 1.2 in that paper assumes, for t0,X>0 and 0<y0<=1:
--   (i) no zeta zero in a declared right-half critical-strip rectangle up to X/2;
--   (ii) no H_t0 zero in a declared final-time right-half-line/canopy region;
--   (iii) no H_t zero in a declared moving intermediate-time barrier region;
-- and concludes Lambda <= t0 + y0^2/2.
--
-- The comparison with DASHI's G2 target is repository-native analysis.  It is
-- NOT a theorem attributed to Polymath and it does not claim that Theorem 1.2
-- supplies the target-centred local-zero exponential-sum estimate.
------------------------------------------------------------------------

data Polymath12Premise : Set where
  initialTimeZetaZeroFreeRectangle : Polymath12Premise
  finalTimeHtZeroFreeCanopy : Polymath12Premise
  intermediateTimeHtBarrier : Polymath12Premise

data Polymath12Conclusion : Set where
  lambdaUpperBound : Polymath12Conclusion

polymath12Reference : String
polymath12Reference =
  "Polymath 2019, Theorem 1.2, DOI 10.1007/s40687-019-0193-1: zero-free initial/final/barrier regions imply Lambda <= t0 + y0^2/2."

------------------------------------------------------------------------
-- Exact target-language comparison.
------------------------------------------------------------------------

data ConsumerLanguage : Set where
  htZeroFreeRegionLanguage : ConsumerLanguage
  targetCenteredLocalZeroOscillatoryIntegralLanguage : ConsumerLanguage

polymathCriterionLanguage : ConsumerLanguage
polymathCriterionLanguage = htZeroFreeRegionLanguage

g2OpenConsumerLanguage : ConsumerLanguage
g2OpenConsumerLanguage = targetCenteredLocalZeroOscillatoryIntegralLanguage

languagesNotDefinitionallyIdentical :
  polymathCriterionLanguage ≡ g2OpenConsumerLanguage → ⊥
languagesNotDefinitionallyIdentical ()

g2TargetReference : String
g2TargetReference = G2.firstUnprovedHarmonicAnalysisTheorem G2.canonicalAristotleG2CurrentCut

------------------------------------------------------------------------
-- Current bridge strength.
------------------------------------------------------------------------

dbnToG2CurrentRelation : Relation.RelationKind
dbnToG2CurrentRelation = Relation.sharedAnalyticProblemDomain

dbnToG2SearchReuse : Relation.ReuseCapability dbnToG2CurrentRelation
dbnToG2SearchReuse = Relation.reuseSharedDomainForSourceSearch

polymathTheorem12DirectlyClosesG2Consumer : Bool
polymathTheorem12DirectlyClosesG2Consumer = false

exactPolymathToG2LemmaBridgeRecovered : Bool
exactPolymathToG2LemmaBridgeRecovered = false

-- The requested term-for-term Theorem 1.3 audit is now owned by
-- DeBruijnNewmanRiemannG2RiemannSiegelBridgeExact.  It finds a real shared
-- analytic domain and a useful DBN finite-evaluation interpretation, but no
-- exact integer-indexed Dirichlet-sum -> zero-indexed G2 consumer transform.
polymathRiemannSiegelApproximationAuditedAgainstG2Kernel : Bool
polymathRiemannSiegelApproximationAuditedAgainstG2Kernel = true

polymathTheorem12DirectlyClosesG2ConsumerIsFalse :
  polymathTheorem12DirectlyClosesG2Consumer ≡ false
polymathTheorem12DirectlyClosesG2ConsumerIsFalse = refl

exactPolymathToG2LemmaBridgeRecoveredIsFalse :
  exactPolymathToG2LemmaBridgeRecovered ≡ false
exactPolymathToG2LemmaBridgeRecoveredIsFalse = refl

polymathRiemannSiegelApproximationAuditedAgainstG2KernelIsTrue :
  polymathRiemannSiegelApproximationAuditedAgainstG2Kernel ≡ true
polymathRiemannSiegelApproximationAuditedAgainstG2KernelIsTrue = refl

riemannSiegelAuditStillFindsNoDirectG2Closure :
  RS.polymath13DirectlyClosesG2 ≡ false
riemannSiegelAuditStillFindsNoDirectG2Closure = RS.polymath13DirectlyClosesG2IsFalse

g2TargetStillOpen :
  G2.targetCenteredLocalZeroExponentialSumBoundClosed
    G2.canonicalAristotleG2CurrentCut ≡ false
g2TargetStillOpen =
  G2.targetCenteredLocalZeroExponentialSumBoundClosedIsFalse
    G2.canonicalAristotleG2CurrentCut

------------------------------------------------------------------------
-- Highest-alpha next bridge search after completing the Theorem 1.3 audit.
--
-- The missing theorem is no longer vaguely "Riemann-Siegel machinery".  It is
-- an explicit transform from xi/H_0 information to the SAME zero-indexed,
-- reflection-paired, target-centred and q-weighted finite consumer used by G2.
------------------------------------------------------------------------

record NextDBNRHAudit : Set where
  constructor nextDBNRHAudit
  field
    sourceTheorem : String
    targetConsumer : String
    requireSameZeroCoordinate : Bool
    requireExactWeightTransport : Bool
    requireErrorBudgetCompatibility : Bool
    theoremAuthorityTransfersBeforeThoseReceipts : Bool
    theoremAuthorityTransfersBeforeThoseReceiptsIsFalse :
      theoremAuthorityTransfersBeforeThoseReceipts ≡ false

canonicalNextDBNRHAudit : NextDBNRHAudit
canonicalNextDBNRHAudit =
  nextDBNRHAudit
    "explicit-formula/Hadamard/log-derivative bridge from xi or H_0 evaluations to the literal finite target-centred zeta-zero carrier"
    g2TargetReference
    true
    true
    true
    false refl
