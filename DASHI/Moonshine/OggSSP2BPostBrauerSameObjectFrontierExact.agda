module DASHI.Moonshine.OggSSP2BPostBrauerSameObjectFrontierExact where

------------------------------------------------------------------------
-- POST-BRAUER 2B SAME-OBJECT FRONTIER
--
-- The all-2-regular-class CTblLib comparison has now passed.  Therefore the
-- actual weight-two 2B Tate head has the same Brauer-character fingerprint as
-- the genuine M24 duad-276 module, and the standard Brauer uniqueness theorem
-- pays the semisimplified/Jordan-Hoelder ingress.
--
-- What is NOT manufactured:
--   * a canonical literal Tate<->duad module isomorphism;
--   * an explicit N <= S <= Tate276 with S/N = 10a or 10b;
--   * descent of the sourced M22:2 outer J2^5 operator to that same S/N;
--   * the two external provenance decisions selecting the Mode5/2T chart.
--
-- This owner is the canonical post-runtime board.  Number-side observers and
-- 30->31->279 remain frozen until the same-object core is inhabited.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSP2BTate276M24BrauerRuntimeReceiptExact as Brauer
import DASHI.Moonshine.OggSSP2BM22RuntimeMaxCutReceiptExact as M22
import DASHI.Moonshine.OggSSP2BM22d2Completion10RuntimeReceiptExact as M22d2
import DASHI.Moonshine.OggSSP2BDefectTwoBitProvenanceSelectorExact as DefectBits
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as FiveIndex

------------------------------------------------------------------------
-- 1. B' semisimplified ingress is now paid by the executed finite calculation.
------------------------------------------------------------------------

brauerTwoRegularClassCount :
  Brauer.twoRegularClassCount Brauer.canonicalTate276M24BrauerRuntimeReceipt ≡ 13
brauerTwoRegularClassCount = Brauer.classCountIsThirteen

brauerAllRowsMatch :
  Brauer.allBrauerRowsMatch Brauer.canonicalTate276M24BrauerRuntimeReceipt ≡ true
brauerAllRowsMatch = Brauer.allBrauerRowsMatchIsTrue

brauerLiftIndependence :
  Brauer.allLiftTracesIndependent Brauer.canonicalTate276M24BrauerRuntimeReceipt ≡ true
brauerLiftIndependence = Brauer.allLiftTracesIndependentIsTrue

semisimplifiedIngressPaid :
  Brauer.semisimplifiedIngressPaid Brauer.canonicalTate276M24BrauerRuntimeReceipt ≡ true
semisimplifiedIngressPaid = Brauer.semisimplifiedIngressIsPaid

literalTateDuadIsomorphismStillOpen :
  Brauer.literalTateDuadIsomorphismPaid Brauer.canonicalTate276M24BrauerRuntimeReceipt ≡ false
literalTateDuadIsomorphismStillOpen = Brauer.literalModuleIsomorphismStillOpen

explicitActualQ10StillOpen :
  Brauer.explicitActualQ10SubquotientPaid Brauer.canonicalTate276M24BrauerRuntimeReceipt ≡ false
explicitActualQ10StillOpen = Brauer.explicitQ10StillOpen

------------------------------------------------------------------------
-- 2. Finite B'/C' target is completely located.
------------------------------------------------------------------------

tenAFiveCopies : M22.factorMultiplicity M22.tenA ≡ 5
tenAFiveCopies = M22.tenAMultiplicityIsFive

tenBFiveCopies : M22.factorMultiplicity M22.tenB ≡ 5
tenBFiveCopies = M22.tenBMultiplicityIsFive

outerJ2x5MatchesTwo : M22d2.outerJ2x5MatchCount ≡ 2
outerJ2x5MatchesTwo = M22d2.outerJ2x5MatchCountIsTwo

------------------------------------------------------------------------
-- 3. D is exactly two provenance decisions, and the convenient NineOrbit
--    indexing cannot pay them because its own owner marks semantic identity false.
------------------------------------------------------------------------

remainingDefectSourceDecisionCount : Nat
remainingDefectSourceDecisionCount = 2

remainingDefectSourceDecisionCountIsTwo :
  remainingDefectSourceDecisionCount ≡ 2
remainingDefectSourceDecisionCountIsTwo = refl

nineOrbitIndexingIsNotSemanticIdentity :
  FiveIndex.orbitToComplementModeIndexingIsSemanticIdentity
    FiveIndex.currentTernary27ReductionBoundary
  ≡ false
nineOrbitIndexingIsNotSemanticIdentity =
  FiveIndex.orbitToComplementModeIndexingIsSemanticIdentityIsFalse

------------------------------------------------------------------------
-- 4. Exact residual same-object witnesses.
------------------------------------------------------------------------

data ExplicitActualTateQ10SubquotientPaid : Set where
data ActualM22d2OuterActionOnSameQPaid : Set where
data TwoBitDefectSourceProvenancePaid : Set where
data ThirtyToP31SameObjectPromotionPaid : Set where
data P31To279SameObjectPromotionPaid : Set where

explicitActualTateQ10StillOpen : ExplicitActualTateQ10SubquotientPaid → ⊥
explicitActualTateQ10StillOpen ()

actualOuterActionOnSameQStillOpen : ActualM22d2OuterActionOnSameQPaid → ⊥
actualOuterActionOnSameQStillOpen ()

twoBitDefectSourceStillOpen : TwoBitDefectSourceProvenancePaid → ⊥
twoBitDefectSourceStillOpen ()

thirtyToP31StillFirewalled : ThirtyToP31SameObjectPromotionPaid → ⊥
thirtyToP31StillFirewalled ()

p31To279StillFirewalled : P31To279SameObjectPromotionPaid → ⊥
p31To279StillFirewalled ()

------------------------------------------------------------------------
-- 5. Canonical status.
------------------------------------------------------------------------

record PostBrauerStatus : Set where
  constructor post-brauer-status
  field
    tateM24BrauerScreenPassed : Bool
    allThirteenRowsMatched : Bool
    liftIndependencePaid : Bool
    semisimplifiedIngressPaid : Bool
    tenAAndTenBJordanHolderContentPaid : Bool
    finiteM22d2OuterJ2x5SourcePaid : Bool
    explicitActualTateQ10SubquotientPaid : Bool
    actualOuterActionOnSameQPaid : Bool
    remainingDefectSourceBits : Nat
    defectSourceSelectionPaid : Bool
    thirtyToP31PromotionPaid : Bool
    p31To279PromotionPaid : Bool
    nextResidual : String

canonicalPostBrauerStatus : PostBrauerStatus
canonicalPostBrauerStatus =
  post-brauer-status
    true true true true true true
    false false
    2 false
    false false
    "Construct one explicit M22:2-stable N<=S<=Hhat0(2B,V2) with S/N=10a or 10b and descended outer J2^5 action; separately source the two remaining Mode5/2T orientation bits. The existing NineOrbit indexing is explicitly non-semantic and cannot pay D."
