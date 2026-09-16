module DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as R

innerInversionReductionRegression :
  (p : Geometry.Ternary27Point) →
  R.reduce27ToPhaseOrbit15 (R.innerInvert27 p) ≡ R.reduce27ToPhaseOrbit15 p
innerInversionReductionRegression = R.reduce27InnerInversionInvariant

canonicalLiftRegression :
  (lane : R.PhaseOrbit15) →
  R.reduce27ToPhaseOrbit15 (R.canonicalLiftPhaseOrbit15 lane) ≡ lane
canonicalLiftRegression = R.reduceCanonicalLift

phasePreservingReductionRegression :
  R.phasePreservingThreeTimesFiveReductionPaid R.currentTernary27ReductionBoundary ≡ true
phasePreservingReductionRegression = R.phasePreservingThreeTimesFiveReductionPaidIsTrue

fullGlobalOrbitCountRegression :
  R.fullGlobalInversionOrbitCount R.currentTernary27ReductionBoundary ≡ 14
fullGlobalOrbitCountRegression = R.fullGlobalInversionOrbitCountIsFourteen

notFullGlobalQuotientRegression :
  R.phasePreservingReductionEqualsFullGlobalInversion R.currentTernary27ReductionBoundary ≡ false
notFullGlobalQuotientRegression = R.phasePreservingReductionEqualsFullGlobalInversionIsFalse

semanticIdentityFirewallRegression :
  R.orbitToComplementModeIndexingIsSemanticIdentity R.currentTernary27ReductionBoundary ≡ false
semanticIdentityFirewallRegression = R.orbitToComplementModeIndexingIsSemanticIdentityIsFalse

monsterAuthorityFirewallRegression :
  R.reducedFifteenIsMonster42dSameObject R.currentTernary27ReductionBoundary ≡ false
monsterAuthorityFirewallRegression = R.reducedFifteenIsMonster42dSameObjectIsFalse
