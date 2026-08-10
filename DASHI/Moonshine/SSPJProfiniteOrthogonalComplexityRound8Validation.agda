module DASHI.Moonshine.SSPJProfiniteOrthogonalComplexityRound8Validation where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)

import DASHI.Moonshine.SSPJStratifiedQuotientRound7Validation
import DASHI.Analysis.NormalizedFibreAveragingExact as Fibre
import DASHI.Analysis.WeightedCoarseFineOrthogonalExact as Orth
import DASHI.Analysis.GlassesProjectionInvolutionExact as Glasses
import DASHI.Foundations.FilteredExtensionSplittingExact as Filtered
import DASHI.Foundations.ClaimScopeCertificateExact as Scope
import DASHI.Biology.IndexedJStratifiedMultiresolutionExact as J
import DASHI.Biology.DecimalResidueTowerExact as Decimal
import DASHI.Biology.DecimalCRTResolutionExact as CRT
import DASHI.Biology.TenAdicInverseLimitBridge as TenAdic
import DASHI.Biology.SignedMultiplicityObstructionExact as Defect
import DASHI.Biology.FRACTRANWreathControlledSymmetryExact as Controlled
import DASHI.Biology.SpectralReachabilityComplexityExact as Complexity
import DASHI.Culture.SignedMultiplicityYinYangBridgeExact as YinYang
import DASHI.Culture.BeliefFibreReplicationExact as Belief
import DASHI.Physics.Common.FiniteWreathRefinementExact as Wreath

------------------------------------------------------------------------
-- Normalized probability fibres and orthogonal coarse/fine split.
------------------------------------------------------------------------

validationFibreMassIsOne : Fibre.fibreMass ≡ 1ℚ
validationFibreMassIsOne = Fibre.fibreMassIsOne

module NF = Fibre.FibreSystem {Base = ⊤}
module WO = Orth.WeightedFibreSystem {Base = ⊤}
module GI = Glasses.GlassesSystem {Base = ⊤}

unitCoarseObservable : NF.CoarseObservable
unitCoarseObservable tt = 1ℚ

validationAveragePullback :
  NF.average (NF.pullback unitCoarseObservable) tt ≡ 1ℚ
validationAveragePullback = NF.averagePullback unitCoarseObservable tt

unitFineObservable : WO.FineObservable
unitFineObservable (tt , Fibre.leftFibre) = 1ℚ
unitFineObservable (tt , Fibre.rightFibre) = 0ℚ

validationProjectionIdempotentLeft :
  WO.P (WO.P unitFineObservable) (tt , Fibre.leftFibre)
  ≡ WO.P unitFineObservable (tt , Fibre.leftFibre)
validationProjectionIdempotentLeft =
  WO.projectionIdempotent unitFineObservable (tt , Fibre.leftFibre)

validationCoarseResidualOrthogonal :
  WO.fineInnerAt tt (WO.P unitFineObservable) (WO.Q unitFineObservable)
  ≡ 0ℚ
validationCoarseResidualOrthogonal =
  WO.projectionResidualOrthogonal tt unitFineObservable

unitGlassObservable : GI.FineObservable
unitGlassObservable (tt , Fibre.leftFibre) = 1ℚ
unitGlassObservable (tt , Fibre.rightFibre) = 0ℚ

validationGlassesInvolution :
  GI.J (GI.J unitGlassObservable) (tt , Fibre.rightFibre)
  ≡ unitGlassObservable (tt , Fibre.rightFibre)
validationGlassesInvolution =
  GI.JInvolutive unitGlassObservable (tt , Fibre.rightFibre)

validationGlassesExchangesPForQ :
  GI.J (GI.P (GI.J unitGlassObservable)) (tt , Fibre.leftFibre)
  ≡ GI.Q unitGlassObservable (tt , Fibre.leftFibre)
validationGlassesExchangesPForQ =
  GI.JPJIsQ unitGlassObservable (tt , Fibre.leftFibre)

validationGlassesDefectZero :
  GI.inversionDefect unitGlassObservable (tt , Fibre.rightFibre) ≡ 0ℚ
validationGlassesDefectZero =
  GI.inversionDefectIsZero unitGlassObservable (tt , Fibre.rightFibre)

------------------------------------------------------------------------
-- Associated-grade count versus explicit split extension.
------------------------------------------------------------------------

validationFilteredCountEleven : 1 + 10 ≡ 11
validationFilteredCountEleven = Filtered.gradedCountSumIsEleven

validationFilteredSection :
  Filtered.ShortExtension.project Filtered.filteredElevenExtension
    (Filtered.SplitExtension.section Filtered.filteredElevenChosenSplit
      Filtered.coarseUnit)
  ≡ Filtered.coarseUnit
validationFilteredSection =
  Filtered.SplitExtension.projectSection
    Filtered.filteredElevenChosenSplit Filtered.coarseUnit

------------------------------------------------------------------------
-- Decimal address -> 10^r residue representatives and finite factorization.
------------------------------------------------------------------------

validationDigitNineRoundTrip :
  Decimal.decodeDigit (Decimal.encodeDigit J.d9) ≡ J.d9
validationDigitNineRoundTrip = Decimal.decodeEncodeDigit J.d9

validationDecimalResidueRoundTrip :
  Decimal.decodeResidue
    (Decimal.encodeResidue (J.extend J.root J.d7))
  ≡ J.extend J.root J.d7
validationDecimalResidueRoundTrip =
  Decimal.decodeEncodeResidue (J.extend J.root J.d7)

validationDecimalPrefixReduction :
  Decimal.encodeResidue
    (J.prefix (J.extend (J.extend J.root J.d3) J.d9))
  ≡ Decimal.reduceResidue
      (Decimal.encodeResidue (J.extend (J.extend J.root J.d3) J.d9))
validationDecimalPrefixReduction =
  Decimal.encodePrefixCompatible
    (J.extend (J.extend J.root J.d3) J.d9)

validationTenPowerFactorOne : 10 ^ 1 ≡ 2 ^ 1 * 5 ^ 1
validationTenPowerFactorOne = CRT.tenPowerFactor 1

validationTenPowerFactorThree : 10 ^ 3 ≡ 2 ^ 3 * 5 ^ 3
validationTenPowerFactorThree = CRT.tenPowerFactor 3

validationCardinalFactorRoundTrip :
  (x : CRT.Residue10 2) →
  CRT.cardinalFactorBackward 2 (CRT.cardinalFactorForward 2 x) ≡ x
validationCardinalFactorRoundTrip = CRT.cardinalFactorBackwardForward 2

------------------------------------------------------------------------
-- Inverse-limit transport is real structure, while CRT arithmetic remains an
-- explicit stronger input rather than a cardinality promotion.
------------------------------------------------------------------------

validationDecimalResidueTowerRoundTripAt :
  (history :
    DASHI.Foundations.StratifiedResolutionTowerExact.InverseLimitPoint
      TenAdic.residue10Tower)
  (r : Nat) →
  DASHI.Foundations.StratifiedResolutionTowerExact.atResolution
    (TenAdic.mapForwardHistory TenAdic.decimalResidueTowerEquivalence
      (TenAdic.mapBackwardHistory TenAdic.decimalResidueTowerEquivalence history))
    r
  ≡ DASHI.Foundations.StratifiedResolutionTowerExact.atResolution history r
validationDecimalResidueTowerRoundTripAt =
  TenAdic.forwardBackwardHistoryAt TenAdic.decimalResidueTowerEquivalence

------------------------------------------------------------------------
-- Signed multiplicity is strictly finer than occurrence and has exact
-- inversion/twisted-inversion laws.
------------------------------------------------------------------------

validationOccurrenceForgetsMultiplicity :
  Defect.presence 1 ≡ Defect.presence 2
validationOccurrenceForgetsMultiplicity = Defect.oneAndTwoHaveSamePresence

validationSignedDefectSurvivesOccurrenceCollision :
  1 Data.Integer.Base.⊖ 2 ≡ Data.Integer.Base.-[1+ 0 ]
validationSignedDefectSurvivesOccurrenceCollision =
  Defect.oneAndTwoHaveNonzeroSignedDefect

validationDefectSwap :
  ∀ {I} (A B : Defect.Multiplicity I) (i : I) →
  Defect.delta B A i ≡ Data.Integer.Base.- (Defect.delta A B i)
validationDefectSwap = Defect.deltaSwap

validationCandidatePolaritySwap :
  ∀ {I} (A B : Defect.Multiplicity I) (i : I) →
  YinYang.polarityOfDefect
    (Defect.orientationOfInteger (Defect.delta B A i))
  ≡ YinYang.reversePolarity
    (YinYang.polarityOfDefect
      (Defect.orientationOfInteger (Defect.delta A B i)))
validationCandidatePolaritySwap = YinYang.swapMultiplicityReversesCandidatePolarity

------------------------------------------------------------------------
-- Arithmetic-controlled finite wreath symmetry.
------------------------------------------------------------------------

validationControlledRuleEnabled :
  Controlled.anyEnabled
    (Controlled.arithmeticState Controlled.canonicalControlledState)
  ≡ true
validationControlledRuleEnabled = Controlled.canonicalControlIsEnabled

validationControlledWreathLeft :
  Controlled.fibreAssignment
    (Controlled.controlledStep Controlled.canonicalControlledState)
    Wreath.leftSite
  ≡ Wreath.neutralState
validationControlledWreathLeft = Controlled.canonicalControlledLeft

validationControlledWreathRight :
  Controlled.fibreAssignment
    (Controlled.controlledStep Controlled.canonicalControlledState)
    Wreath.rightSite
  ≡ Wreath.positiveState
validationControlledWreathRight = Controlled.canonicalControlledRight

validationBinaryEncodingRecoversTriState :
  (state : Wreath.TriState) →
  Controlled.decodeTriState (Controlled.encodeTriState state) ≡ state
validationBinaryEncodingRecoversTriState = Controlled.decodeEncodeTriState

------------------------------------------------------------------------
-- Reachability obstruction and cost interface.
------------------------------------------------------------------------

validationReachabilityInvariant :
  ∀ {State Value} {Step : State → State → Set}
    (invariant : Complexity.StepInvariant Step Value)
    {n x y} → Complexity.ReachIn Step n x y →
  Complexity.Φ invariant x ≡ Complexity.Φ invariant y
validationReachabilityInvariant = Complexity.reachPreservesInvariant

validationPotentialBudget :
  ∀ {State} {Step : State → State → Set}
    (pot : Complexity.StepPotential Step)
    {n x y} → Complexity.ReachIn Step n x y →
  Complexity.potential pot y
  ≤ Complexity.potential pot x + n * Complexity.perStepCost pot
validationPotentialBudget = Complexity.reachPotentialBound

------------------------------------------------------------------------
-- Belief-coordinate fibre independence is a conditional product theorem, not
-- an empirical assertion.
------------------------------------------------------------------------

validationBeliefFibreIndependence :
  ∀ {Material BeliefState}
    (dynamics : Belief.FibreInsensitiveDynamics Material BeliefState)
    (material : Material) (b1 b2 : BeliefState) →
  Belief.projectMaterial (Belief.stepFine dynamics (material , b1))
  ≡ Belief.projectMaterial (Belief.stepFine dynamics (material , b2))
validationBeliefFibreIndependence = Belief.beliefLiesInTransitionFibre

------------------------------------------------------------------------
-- Claim-scope semantics: not-claimed-here and mathematical refutation are
-- separate types.
------------------------------------------------------------------------

validationLegacyBoundaryIsNotRefutationFlag :
  Scope.BoundarySemanticsClaimScope.legacyFalseFlagShouldBeReadAsImpossibilityProof
    Scope.canonicalBoundarySemanticsClaimScope
  ≡ false
validationLegacyBoundaryIsNotRefutationFlag = refl
