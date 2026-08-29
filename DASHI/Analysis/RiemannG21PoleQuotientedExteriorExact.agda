module DASHI.Analysis.RiemannG21PoleQuotientedExteriorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannHermitianTopDownAssemblyExact as G1G4
import DASHI.Analysis.PoleQuotientedExteriorDeskTestExact as RankOneExterior
import DASHI.Analysis.PoleRankTwoQuotientedExteriorDeskTestExact as RankTwoExterior
import DASHI.Analysis.RiemannG21LiteralPoleRankAuditExact as PoleAudit
import DASHI.Analysis.RiemannG21PoleMainModeSeparationExact as MainMode
import DASHI.Analysis.RiemannG21ConjugateHeightSourceBridgeExact as Heights
import DASHI.Analysis.RiemannG21SymmetricSampleBlockReductionExact as Blocks
import DASHI.Analysis.StrictKernelMomentRatioExact as TP2
import DASHI.Analysis.RiemannG21OddSinhTP2Exact as OddTP2
import DASHI.Analysis.RiemannG21DeterminantMarginTransferExact as Margin
import DASHI.Analysis.RiemannG21OffLinePoleQuotientTransversalityExact as ZeroTrans
import DASHI.Analysis.RiemannWeilOffLineHyperbolicBlockExact as Hyperbolic
import DASHI.Analysis.RiemannG21PrimePairKernelExact as Pair
import DASHI.Analysis.RiemannG21TwoByTwoMixedObstructionExact as Mixed2
import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Det3

data G21Obligation : Set where
  literalTwoPoleAudit : G21Obligation
  poleToPrimeMainModeTransport : G21Obligation
  optionalRankOnePoleReduction : G21Obligation
  rankTwoFourSamplePoleQuotientIdentity : G21Obligation
  sourceOffLineHyperbolicPair : G21Obligation
  conjugateHeightSourceGeometry : G21Obligation
  symmetricSampleParityBlockReduction : G21Obligation
  strictSinhTP2OddKernel : G21Obligation
  strictOddMomentDeterminant : G21Obligation
  directDeterminantMarginTransfer : G21Obligation
  actualTaperEvenHeightMinor : G21Obligation
  actualTaperOddHeightMinor : G21Obligation
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
poleAuditEntry = g21ObligationEntry literalTwoPoleAudit sourceAudited
  "The companion literature-form explicit formula contains h(i/2)+h(-i/2), so the literal Weil pole nuisance has two evaluation roles before further transport."

mainModeTransportEntry : G21ObligationEntry
mainModeTransportEntry = g21ObligationEntry poleToPrimeMainModeTransport analyticInterfaceOpen
  "G20's deterministic prime-counting/PNT main mode is not definitionally the literal two-evaluation Weil pole term. A justified transform must identify the actual post-unfolding nuisance span."

rankOneReductionEntry : G21ObligationEntry
rankOneReductionEntry = g21ObligationEntry optionalRankOnePoleReduction analyticInterfaceOpen
  "If the actual post-unfolding nuisance profiles factor through one common profile, the optimized three-sample quotient is available. Conjugacy alone is not rank one."

rankTwoQuotientEntry : G21ObligationEntry
rankTwoQuotientEntry = g21ObligationEntry rankTwoFourSamplePoleQuotientIdentity analyticInterfaceOpen
  "Fail-closed fallback: if two nuisance directions remain, use four samples and quotient both before estimation."

sourceHyperbolicEntry : G21ObligationEntry
sourceHyperbolicEntry = g21ObligationEntry sourceOffLineHyperbolicPair structurallyDerived
  "PR #604 already owns the source-native off-line reflection pair as a two-direction hyperbolic block with one positive and one negative direction."

heightGeometryEntry : G21ObligationEntry
heightGeometryEntry = g21ObligationEntry conjugateHeightSourceGeometry sourceAudited
  "The real-even taper makes pole and off-line reflection evaluations conjugate-height response pairs without implying their sampled vectors are independent."

parityBlockEntry : G21ObligationEntry
parityBlockEntry = g21ObligationEntry symmetricSampleParityBlockReduction structurallyDerived
  "Symmetric samples r1,-r1,r2,-r2 reduce the four-vector problem to independent even/cosh and odd/sinh 2x2 minors."

sinhTP2Entry : G21ObligationEntry
sinhTP2Entry = g21ObligationEntry strictSinhTP2OddKernel analyticInterfaceOpen
  "Prove the atomic odd kernel theorem sinh(pv)sinh(au) > sinh(pu)sinh(av) for 0<a<p and 0<u<v. This is strict TP2 of K(a,u)=sinh(au) on the positive quadrant."

oddMomentEntry : G21ObligationEntry
oddMomentEntry = g21ObligationEntry strictOddMomentDeterminant analyticInterfaceOpen
  "Use strict sinh TP2 and positive nondegenerate taper support in the symmetrized double-integral identity to prove N1(a)N3(p) > N3(a)N1(p), equivalently strict negativity in the old G21 determinant orientation."

marginEntry : G21ObligationEntry
marginEntry = g21ObligationEntry directDeterminantMarginTransfer analyticInterfaceOpen
  "Extract a strict continuum determinant margin Delta and prove the actual finite-radius determinant satisfies |D_R-Delta|<Delta, preserving sign without four independent entrywise estimates."

evenMinorEntry : G21ObligationEntry
evenMinorEntry = g21ObligationEntry actualTaperEvenHeightMinor analyticInterfaceOpen
  "Close the easier even/cosh signed moment/minor lane, preferably through the direct product-to-sum TP2 route plus the same generic strict-kernel moment-composition owner."

oddMinorEntry : G21ObligationEntry
oddMinorEntry = g21ObligationEntry actualTaperOddHeightMinor analyticInterfaceOpen
  "Use the strict odd continuum determinant and determinant-margin transfer to obtain a nonzero finite-radius odd parity minor at explicit symmetric radii."

zeroTransversalityEntry : G21ObligationEntry
zeroTransversalityEntry = g21ObligationEntry offLinePoleQuotientTransversality analyticInterfaceOpen
  "Combine the literal nuisance-space transport with both signed parity minors to obtain rank-two off-line response modulo the full nuisance span."

explicitFormulaEntry : G21ObligationEntry
explicitFormulaEntry = g21ObligationEntry literalTwoChannelExplicitFormulaExpansion arithmeticInterfaceOpen
  "Only after zero-side transversality closes, substitute both literal explicit formulas before majorization and derive the surviving double von-Mangoldt pair expression exactly."

diagonalZeroEntry : G21ObligationEntry
diagonalZeroEntry = g21ObligationEntry literalPrimePairDiagonalZero arithmeticInterfaceOpen
  "For a derivative/contrastive channel derive the expected log(n/m)-type factor and prove K(n,n)=0 on the literal pair kernel."

nonseparableEntry : G21ObligationEntry
nonseparableEntry = g21ObligationEntry literalPrimePairRelationalNonseparability arithmeticInterfaceOpen
  "Prove a rectangle violation and preferably a nonzero 2x2 minor for the literal prime-pair kernel."

swapEntry : G21ObligationEntry
swapEntry = g21ObligationEntry exactSwapReindexBeforeMajorization arithmeticInterfaceOpen
  "Split the exact pair carrier into diagonal and swapped off-diagonal fibres and reindex before any absolute-value bound."

scaleEntry : G21ObligationEntry
scaleEntry = g21ObligationEntry primePairScaleDecision arithmeticInterfaceOpen
  "Only after exact nuisance/diagonal cancellation, compare the trivial surviving pair scale with the zero-side determinant floor and kill the lane if the ratio diverges."

canonicalG21Obligations : List G21ObligationEntry
canonicalG21Obligations =
  poleAuditEntry ∷ mainModeTransportEntry ∷ rankOneReductionEntry
  ∷ rankTwoQuotientEntry ∷ sourceHyperbolicEntry ∷ heightGeometryEntry
  ∷ parityBlockEntry ∷ sinhTP2Entry ∷ oddMomentEntry ∷ marginEntry
  ∷ evenMinorEntry ∷ oddMinorEntry ∷ zeroTransversalityEntry
  ∷ explicitFormulaEntry ∷ diagonalZeroEntry ∷ nonseparableEntry
  ∷ swapEntry ∷ scaleEntry ∷ []

optimizedThreeSampleResidualDimension : PoleAudit.residualDimension PoleAudit.rankOneThreeSampleCase ≡ 2
optimizedThreeSampleResidualDimension = refl

literalGenericThreeSampleResidualDimension : PoleAudit.residualDimension PoleAudit.genericTwoPoleThreeSampleCase ≡ 1
literalGenericThreeSampleResidualDimension = PoleAudit.threeSamplesNeedRankOneReductionForTwoResidualDimensions

robustFourSampleResidualDimension : PoleAudit.residualDimension PoleAudit.genericTwoPoleFourSampleCase ≡ 2
robustFourSampleResidualDimension = PoleAudit.fourSamplesSupportTwoResidualDimensionsWithoutRankOneReduction

sourceOffLinePairHasPositiveDirection : Hyperbolic.positiveIndexBeforePullback ZeroTrans.canonicalSourceHyperbolicPair ≡ 1
sourceOffLinePairHasPositiveDirection = ZeroTrans.sourceHasPositiveDirection

sourceOffLinePairHasNegativeDirection : Hyperbolic.negativeIndexBeforePullback ZeroTrans.canonicalSourceHyperbolicPair ≡ 1
sourceOffLinePairHasNegativeDirection = ZeroTrans.sourceHasNegativeDirection

conjugateHeightSymmetryDoesNotForceSeparation :
  Heights.responseAtHeight Heights.canonicalCollapsedConjugateFamily Heights.lowHeight
  ≡ Heights.responseAtHeight Heights.canonicalCollapsedConjugateFamily Heights.highHeight
conjugateHeightSymmetryDoesNotForceSeparation = Heights.collapsedHeightResponsesEqual

symmetricParityAdmissionCriterionIsNonVacuous : Blocks.SymmetricSampleTwoHeightAdmission
symmetricParityAdmissionCriterionIsNonVacuous = Blocks.canonicalSymmetricSampleAdmission

evenMinorAloneDoesNotForceOddMinor :
  Blocks.MinorNonzero (Blocks.oddMinor Blocks.evenOnlyOffLine Blocks.evenOnlyPole) → ⊥
evenMinorAloneDoesNotForceOddMinor = Blocks.evenOnlyOddMinorFails

genericStrictTP2OwnerBoundary : TP2.StrictKernelMomentRatioBoundary
genericStrictTP2OwnerBoundary = TP2.canonicalStrictKernelMomentRatioBoundary

oddSinhTP2Boundary : OddTP2.OddSinhTP2Boundary
oddSinhTP2Boundary = OddTP2.canonicalOddSinhTP2Boundary

determinantMarginBoundary : Margin.DeterminantMarginBoundary
determinantMarginBoundary = Margin.canonicalDeterminantMarginBoundary

zeroTransversalityCriterionIsNonVacuous : ZeroTrans.OffLinePoleQuotientTransversality
zeroTransversalityCriterionIsNonVacuous = ZeroTrans.canonicalToyTransversality

naiveTwoByTwoRankOnePoleGateRejected :
  Mixed2.det2Code Mixed2.responseLeft Mixed2.responseRight
  ≡ Mixed2.det2Code Mixed2.commonPole Mixed2.commonPole → ⊥
naiveTwoByTwoRankOnePoleGateRejected = Mixed2.rankOnePoleDoesNotKillMixedTwoByTwoDeterminant

finiteThreeByThreeRankOneMechanism :
  Det3.SameSignedDeterminant
    (Det3.det3 Det3.response₁ Det3.response₂ Det3.poleProfile)
    (Det3.det3 Det3.residual₁ Det3.residual₂ Det3.poleProfile)
finiteThreeByThreeRankOneMechanism = Det3.augmentedPoleQuotientPreservesSignedDeterminant

primePairRelationalAdmissionCriterionIsNonVacuous : Pair.PrimePairRelationalAdmission
primePairRelationalAdmissionCriterionIsNonVacuous = Pair.canonicalToyPrimePairRelationalAdmission

pairSwapIsInvolutive : {A : Set} → (p : Pair.Pair A) → Pair.swapPair (Pair.swapPair p) ≡ p
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
    conjugateHeightGeometrySourceAudited : Bool
    conjugateHeightGeometrySourceAuditedIsTrue : conjugateHeightGeometrySourceAudited ≡ true
    symmetricSampleParityBlockReductionDerived : Bool
    symmetricSampleParityBlockReductionDerivedIsTrue : symmetricSampleParityBlockReductionDerived ≡ true
    genericStrictTP2MomentOwnerConstructed : Bool
    genericStrictTP2MomentOwnerConstructedIsTrue : genericStrictTP2MomentOwnerConstructed ≡ true
    determinantMarginInterfaceConstructed : Bool
    determinantMarginInterfaceConstructedIsTrue : determinantMarginInterfaceConstructed ≡ true
    actualSinhTP2Derived : Bool
    actualSinhTP2DerivedIsFalse : actualSinhTP2Derived ≡ false
    actualOddMomentStrictSignDerived : Bool
    actualOddMomentStrictSignDerivedIsFalse : actualOddMomentStrictSignDerived ≡ false
    actualTaperEvenHeightMinorDerived : Bool
    actualTaperEvenHeightMinorDerivedIsFalse : actualTaperEvenHeightMinorDerived ≡ false
    actualTaperOddHeightMinorDerived : Bool
    actualTaperOddHeightMinorDerivedIsFalse : actualTaperOddHeightMinorDerived ≡ false
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
    true refl false refl false refl true refl true refl true refl true refl
    true refl true refl
    false refl false refl false refl false refl false refl false refl false refl false refl
