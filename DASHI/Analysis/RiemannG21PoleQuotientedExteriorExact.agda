module DASHI.Analysis.RiemannG21PoleQuotientedExteriorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannHermitianTopDownAssemblyExact as G1G4
import DASHI.Analysis.PoleQuotientedExteriorDeskTestExact as RankOneExterior
import DASHI.Analysis.PoleRankTwoQuotientedExteriorDeskTestExact as RankTwoExterior
import DASHI.Analysis.RiemannG21LiteralPoleRankAuditExact as PoleAudit
import DASHI.Analysis.RiemannG21PoleMainModeSeparationExact as MainMode
import DASHI.Analysis.RiemannG21OffLinePoleQuotientTransversalityExact as ZeroTrans
import DASHI.Analysis.RiemannG21PrimePairKernelExact as Pair
import DASHI.Analysis.RiemannG21TwoByTwoMixedObstructionExact as Mixed2
import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Det3

data G21Obligation : Set where
  literalTwoPoleAudit : G21Obligation
  poleToPrimeMainModeTransport : G21Obligation
  optionalRankOnePoleReduction : G21Obligation
  rankTwoFourSamplePoleQuotientIdentity : G21Obligation
  sourceOffLineHyperbolicPair : G21Obligation
  offLinePoleQuotientTransversality : G21Obligation
  literalTwoChannelExplicitFormulaExpansion : G21Obligation
  literalPrimePairDiagonalZero : G21Obligation
  literalPrimePairRelationalNonseparability : G21Obligation
  exactSwapReindexBeforeMajorization : G21Obligation
  primePairScaleDecision : G21Obligation

data G21Status : Set where
  structurallyDerived : G21Status
  sourceAudited : G21Status
  analyticInterfaceOpen : G21Status
  arithmeticInterfaceOpen : G21Status
  rejectedByExactCounterexample : G21Status

record G21ObligationEntry : Set where
  constructor g21ObligationEntry
  field
    obligation : G21Obligation
    status : G21Status
    reading : String

open G21ObligationEntry public

poleAuditEntry : G21ObligationEntry
poleAuditEntry =
  g21ObligationEntry literalTwoPoleAudit sourceAudited
    "The companion literature-form explicit formula contains h(i/2)+h(-i/2). The literal Weil pole nuisance therefore has two evaluation roles before any further transform."

mainModeTransportEntry : G21ObligationEntry
mainModeTransportEntry =
  g21ObligationEntry poleToPrimeMainModeTransport analyticInterfaceOpen
    "G20's deterministic prime-counting/PNT main mode is not definitionally the literal two-evaluation Weil pole term. A justified explicit-formula/partial-summation bridge must identify which nuisance directions survive in the post-unfolding prime observer."

rankOneReductionEntry : G21ObligationEntry
rankOneReductionEntry =
  g21ObligationEntry optionalRankOnePoleReduction analyticInterfaceOpen
    "If the actual post-unfolding nuisance profiles factor through one common profile, the optimized three-sample quotient is available. Conjugacy alone is not promoted to complex-linear dependence."

rankTwoQuotientEntry : G21ObligationEntry
rankTwoQuotientEntry =
  g21ObligationEntry rankTwoFourSamplePoleQuotientIdentity analyticInterfaceOpen
    "Fail-closed fallback: if two nuisance directions remain, use four samples and quotient both; prove the literal 4x4 augmented determinant equals the residual determinant before estimation."

sourceHyperbolicEntry : G21ObligationEntry
sourceHyperbolicEntry =
  g21ObligationEntry sourceOffLineHyperbolicPair structurallyDerived
    "PR #604 already owns the source-native off-line reflection pair as a two-direction hyperbolic block with one positive and one negative direction."

zeroTransversalityEntry : G21ObligationEntry
zeroTransversalityEntry =
  g21ObligationEntry offLinePoleQuotientTransversality analyticInterfaceOpen
    "The new zero-side theorem is not source signature (1,1) but transversality: the two off-line response directions must remain independent modulo the full nuisance pole/main-mode span. The four-vector exterior criterion is now explicit and executable."

explicitFormulaEntry : G21ObligationEntry
explicitFormulaEntry =
  g21ObligationEntry literalTwoChannelExplicitFormulaExpansion arithmeticInterfaceOpen
    "Substitute both literal explicit formulas before majorization and derive the surviving double von-Mangoldt pair expression exactly."

diagonalZeroEntry : G21ObligationEntry
diagonalZeroEntry =
  g21ObligationEntry literalPrimePairDiagonalZero arithmeticInterfaceOpen
    "For a derivative/contrastive channel derive the expected log(n/m)-type factor and prove K(n,n)=0 on the literal pair kernel."

nonseparableEntry : G21ObligationEntry
nonseparableEntry =
  g21ObligationEntry literalPrimePairRelationalNonseparability arithmeticInterfaceOpen
    "Prove a rectangle violation and preferably a nonzero 2x2 minor for the literal pair kernel."

swapEntry : G21ObligationEntry
swapEntry =
  g21ObligationEntry exactSwapReindexBeforeMajorization arithmeticInterfaceOpen
    "Split the exact pair carrier into diagonal and swapped off-diagonal fibres and reindex before any absolute-value bound."

scaleEntry : G21ObligationEntry
scaleEntry =
  g21ObligationEntry primePairScaleDecision arithmeticInterfaceOpen
    "Only after exact nuisance/diagonal cancellation, compare the trivial surviving pair scale with the zero-side determinant floor and kill the lane if the ratio diverges."

canonicalG21Obligations : List G21ObligationEntry
canonicalG21Obligations =
  poleAuditEntry ∷ mainModeTransportEntry ∷ rankOneReductionEntry
  ∷ rankTwoQuotientEntry ∷ sourceHyperbolicEntry ∷ zeroTransversalityEntry
  ∷ explicitFormulaEntry ∷ diagonalZeroEntry ∷ nonseparableEntry
  ∷ swapEntry ∷ scaleEntry ∷ []

optimizedThreeSampleResidualDimension :
  PoleAudit.residualDimension PoleAudit.rankOneThreeSampleCase ≡ 2
optimizedThreeSampleResidualDimension = refl

literalGenericThreeSampleResidualDimension :
  PoleAudit.residualDimension PoleAudit.genericTwoPoleThreeSampleCase ≡ 1
literalGenericThreeSampleResidualDimension =
  PoleAudit.threeSamplesNeedRankOneReductionForTwoResidualDimensions

robustFourSampleResidualDimension :
  PoleAudit.residualDimension PoleAudit.genericTwoPoleFourSampleCase ≡ 2
robustFourSampleResidualDimension =
  PoleAudit.fourSamplesSupportTwoResidualDimensionsWithoutRankOneReduction

sourceOffLinePairHasPositiveDirection :
  HyperbolicPositive : Set
sourceOffLinePairHasPositiveDirection = ⊤
  where
  HyperbolicPositive =
    ZeroTrans.Hyperbolic.positiveIndexBeforePullback
      ZeroTrans.canonicalSourceHyperbolicPair ≡ 1

sourceOffLinePairHasNegativeDirection :
  ZeroTrans.Hyperbolic.negativeIndexBeforePullback
    ZeroTrans.canonicalSourceHyperbolicPair ≡ 1
sourceOffLinePairHasNegativeDirection = ZeroTrans.sourceHasNegativeDirection

zeroTransversalityCriterionIsNonVacuous : ZeroTrans.OffLinePoleQuotientTransversality
zeroTransversalityCriterionIsNonVacuous = ZeroTrans.canonicalToyTransversality

naiveTwoByTwoRankOnePoleGateRejected :
  Mixed2.det2Code Mixed2.responseLeft Mixed2.responseRight
  ≡ Mixed2.det2Code Mixed2.commonPole Mixed2.commonPole → ⊥
naiveTwoByTwoRankOnePoleGateRejected =
  Mixed2.rankOnePoleDoesNotKillMixedTwoByTwoDeterminant

finiteThreeByThreeRankOneMechanism :
  Det3.SameSignedDeterminant
    (Det3.det3 Det3.response₁ Det3.response₂ Det3.poleProfile)
    (Det3.det3 Det3.residual₁ Det3.residual₂ Det3.poleProfile)
finiteThreeByThreeRankOneMechanism =
  Det3.augmentedPoleQuotientPreservesSignedDeterminant

primePairRelationalAdmissionCriterionIsNonVacuous : Pair.PrimePairRelationalAdmission
primePairRelationalAdmissionCriterionIsNonVacuous = Pair.canonicalToyPrimePairRelationalAdmission

pairSwapIsInvolutive :
  {A : Set} → (p : Pair.Pair A) → Pair.swapPair (Pair.swapPair p) ≡ p
pairSwapIsInvolutive = Pair.swapPairInvolutive

record G21CurrentBoundary : Set where
  constructor g21CurrentBoundary
  field
    literalSourceHasTwoPoleEvaluations : Bool
    literalSourceHasTwoPoleEvaluationsIsTrue : literalSourceHasTwoPoleEvaluations ≡ true
    poleToPrimeMainModeTransportDerived : Bool
    poleToPrimeMainModeTransportDerivedIsFalse : poleToPrimeMainModeTransportDerived ≡ false
    rankOnePoleReductionDerived : Bool
    rankOnePoleReductionDerivedIsFalse : rankOnePoleReductionDerived ≡ false
    robustRankTwoFourSampleCarrierConstructed : Bool
    robustRankTwoFourSampleCarrierConstructedIsTrue : robustRankTwoFourSampleCarrierConstructed ≡ true
    sourceOffLineHyperbolicPairOwned : Bool
    sourceOffLineHyperbolicPairOwnedIsTrue : sourceOffLineHyperbolicPairOwned ≡ true
    literalPoleQuotientTransversalityDerived : Bool
    literalPoleQuotientTransversalityDerivedIsFalse : literalPoleQuotientTransversalityDerived ≡ false
    literalPrimePairKernelDerived : Bool
    literalPrimePairKernelDerivedIsFalse : literalPrimePairKernelDerived ≡ false
    favorableScaleGateDerived : Bool
    favorableScaleGateDerivedIsFalse : favorableScaleGateDerived ≡ false
    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

canonicalG21CurrentBoundary : G21CurrentBoundary
canonicalG21CurrentBoundary =
  g21CurrentBoundary
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
