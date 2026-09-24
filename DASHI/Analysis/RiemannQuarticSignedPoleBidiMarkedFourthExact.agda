module DASHI.Analysis.RiemannQuarticSignedPoleBidiMarkedFourthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH BIDI MARKED FOURTH-ANGULAR OWNER
--
-- Lean companion:
--
--   Synthesis/
--   RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean
--
-- This owner records the first genuinely useful bridge between the live
-- fourth-angular RH obstruction and Montgomery-type marked pair machinery.
--
-- Backward / Clay-facing side:
--
--   A4_local
--     =
--   sum_local m_sigma Re(a_sigma + i delta_sigma)^4
--     - local smooth-mu vertical fourth moment.
--
-- The zero part splits exactly into a centred vertical fourth moment plus
-- the horizontal correction
--
--   sum m delta^4 - integral delta^4 mu
--     + sum m a^2(a^2 - 6 delta^2).
--
-- Forward / pair-difference side:
--
-- Let the target zero have horizontal displacement A and let its horizontal
-- functional-equation reflection have displacement -A.  For
--
--   P2(x,d) = Re(x+i d)^2,
--   P4(x,d) = Re(x+i d)^4,
--
-- Lean proves the pointwise identity
--
--   P4(a,d)
--     =
--   1/2 * [ P4(a-A,d) + P4(a+A,d) ]
--     - 3*A^2 * [ P2(a-A,d) + P2(a+A,d) ]
--     + 5*A^4.
--
-- Hence the local target-centred fourth angular statistic is reconstructed
-- from only the 0th, 2nd and 4th EVEN marked pair-difference moments around
-- the target and its horizontal reflection.  Odd derivatives/moments are
-- not required.
--
-- This is the current bidi intersection:
--
--   desired target-centred cos(4 theta) statistic
--       <-> even marked pair moments of orders 0,2,4.
--
-- What remains new mathematics is a one-centre LOCALIZED marked
-- pair-correlation / explicit-formula estimate strong enough to control those
-- moments with the required sign and to couple them to the exact far source.
------------------------------------------------------------------------

data BidiMarkedFourthCoordinate : Set where
  centredLocalFourthAngularDefinition : BidiMarkedFourthCoordinate
  verticalPlusHorizontalCentredSplit : BidiMarkedFourthCoordinate
  targetReflectionPointwiseFourthReconstruction :
    BidiMarkedFourthCoordinate
  evenZeroTwoFourMarkedMomentsSuffice :
    BidiMarkedFourthCoordinate
  universalZeroTwoFourBidiOperator :
    BidiMarkedFourthCoordinate
  smoothMuBackgroundUsesSameBidiOperator :
    BidiMarkedFourthCoordinate

  localizedOneCentreMarkedPairProducer :
    BidiMarkedFourthCoordinate
  markedPairPrimeSideSignOrBound :
    BidiMarkedFourthCoordinate
  centredFourthAngularBias :
    BidiMarkedFourthCoordinate
  fourthAngularFarCouplingPaysG3 :
    BidiMarkedFourthCoordinate

data BidiMarkedFourthStatus : Set where
  theoremOwned : BidiMarkedFourthStatus
  openAnalyticObstruction : BidiMarkedFourthStatus

bidiMarkedFourthStatus :
  BidiMarkedFourthCoordinate -> BidiMarkedFourthStatus
bidiMarkedFourthStatus centredLocalFourthAngularDefinition = theoremOwned
bidiMarkedFourthStatus verticalPlusHorizontalCentredSplit = theoremOwned
bidiMarkedFourthStatus targetReflectionPointwiseFourthReconstruction =
  theoremOwned
bidiMarkedFourthStatus evenZeroTwoFourMarkedMomentsSuffice = theoremOwned
bidiMarkedFourthStatus universalZeroTwoFourBidiOperator = theoremOwned
bidiMarkedFourthStatus smoothMuBackgroundUsesSameBidiOperator = theoremOwned

bidiMarkedFourthStatus localizedOneCentreMarkedPairProducer =
  openAnalyticObstruction
bidiMarkedFourthStatus markedPairPrimeSideSignOrBound =
  openAnalyticObstruction
bidiMarkedFourthStatus centredFourthAngularBias =
  openAnalyticObstruction
bidiMarkedFourthStatus fourthAngularFarCouplingPaysG3 =
  openAnalyticObstruction

record BidiMarkedFourthBoundary : Set where
  constructor bidi-marked-fourth-boundary
  field
    centredLocalFourthAngularDefinitionPaid : Bool
    verticalPlusHorizontalCentredSplitPaid : Bool
    targetReflectionPointwiseFourthReconstructionPaid : Bool
    evenZeroTwoFourMarkedMomentsSufficePaid : Bool
    universalZeroTwoFourBidiOperatorPaid : Bool
    smoothMuBackgroundUsesSameBidiOperatorPaid : Bool

    localizedOneCentreMarkedPairProducerPaid : Bool
    markedPairPrimeSideSignOrBoundPaid : Bool
    centredFourthAngularBiasPaid : Bool
    fourthAngularFarCouplingPaysG3Paid : Bool

    centredLocalFourthAngularDefinitionPaidIsTrue :
      centredLocalFourthAngularDefinitionPaid ≡ true
    verticalPlusHorizontalCentredSplitPaidIsTrue :
      verticalPlusHorizontalCentredSplitPaid ≡ true
    targetReflectionPointwiseFourthReconstructionPaidIsTrue :
      targetReflectionPointwiseFourthReconstructionPaid ≡ true
    evenZeroTwoFourMarkedMomentsSufficePaidIsTrue :
      evenZeroTwoFourMarkedMomentsSufficePaid ≡ true
    universalZeroTwoFourBidiOperatorPaidIsTrue :
      universalZeroTwoFourBidiOperatorPaid ≡ true
    smoothMuBackgroundUsesSameBidiOperatorPaidIsTrue :
      smoothMuBackgroundUsesSameBidiOperatorPaid ≡ true

    localizedOneCentreMarkedPairProducerPaidIsFalse :
      localizedOneCentreMarkedPairProducerPaid ≡ false
    markedPairPrimeSideSignOrBoundPaidIsFalse :
      markedPairPrimeSideSignOrBoundPaid ≡ false
    centredFourthAngularBiasPaidIsFalse :
      centredFourthAngularBiasPaid ≡ false
    fourthAngularFarCouplingPaysG3PaidIsFalse :
      fourthAngularFarCouplingPaysG3Paid ≡ false

    interpretation : String
    nextResearchCut : String

canonicalBidiMarkedFourthBoundary :
  BidiMarkedFourthBoundary
canonicalBidiMarkedFourthBoundary =
  bidi-marked-fourth-boundary
    true true true true true true
    false false false false
    refl refl refl refl refl refl
    refl refl refl refl
    "The live RH obstruction is now expressed both backward from G3 as a smooth-mu-centred fourth angular statistic and forward toward Montgomery machinery as even target/reflection marked pair moments.  The exact algebraic bridge needs only orders 0, 2 and 4: P4(a,d)=1/2(P4(a-A,d)+P4(a+A,d))-3*A^2(P2(a-A,d)+P2(a+A,d))+5*A^4.  These moments are consumed by one universal bidi operator D_A(M0,M2,M4)=1/2*M4-3*A^2*M2+5*A^4*M0.  The smooth critical-line mu background obeys the same operator with a=0, so the centred zero-minus-mu statistic has a single marked-transform interface.  Odd marked derivatives are not required."
    "Do not add more compensation bookkeeping.  The next Clay-relevant mathematics is a target-centred localized marked pair producer, together with a prime-side estimate strong enough to control its even 2nd/4th moments uniformly around an arbitrary hypothetical off-line zero.  Preserve FarExact with sign.  If this marked local theorem cannot be obtained, redesign the witness rather than adding representation layers."

targetReflectionBidiBridgeIsPaid :
  bidiMarkedFourthStatus targetReflectionPointwiseFourthReconstruction
    ≡ theoremOwned
targetReflectionBidiBridgeIsPaid = refl

evenMarkedMomentsAreTheInterface :
  bidiMarkedFourthStatus evenZeroTwoFourMarkedMomentsSuffice
    ≡ theoremOwned
evenMarkedMomentsAreTheInterface = refl

localizedMarkedPairProducerRemainsOpen :
  bidiMarkedFourthStatus localizedOneCentreMarkedPairProducer
    ≡ openAnalyticObstruction
localizedMarkedPairProducerRemainsOpen = refl


------------------------------------------------------------------------
-- SHORT-SUPPORT BIDI MARKED-POLE CURVATURE FRONTIER
--
-- The live Lean programme has moved beyond the earlier Montgomery-style
-- producer hypothesis.
--
-- Horizontal cosh marking of the ACTUAL four-window detector preserves its
-- support below log 2.  Hence the literal Weil prime projective channel
-- remains exactly zero for every mark parameter A.
--
-- The first nontrivial marked information is therefore the pole/archimedean
-- channel.  After v=(t/16)u normalization the physical mark is
--
--   cosh((16*A/t) v).
--
-- Its quadratic carrier at an endpoint is the derivative determinant
-- obtained by inserting v^2 once in each of the two determinant columns.
--
-- Lean now proves:
--
-- * atomic endpoint signs on the exact J2-null roots:
--
--     Q_half > 0,
--     Q_twoThird < 0;
--
-- * those signs persist uniformly on the FULL existing mu corridor;
--
-- * sufficiently narrow smooth windows preserve those two endpoint signs;
--
-- * individual smooth pole coordinates are positive on a common radius;
--
-- * there exists a strengthened ordinary QuarticFourSignedPolePair W with
--   the old 7*pi^4/1600 target-strength floor AND
--
--     D_twoThird * Q_half - D_half * Q_twoThird > 0;
--
-- * the literal physical marked pole channel is exactly
--
--     4*(16/t)^2 * normalizedMarkedPoleDeterminant;
--
-- * replacing each cosh(Bv) by 1+B^2 v^2/2 gives the exact determinant
--   truncation
--
--     D_trunc(B)
--       = D0 + (B^2/2) Q + (B^4/4) D2;
--
--   after the signed endpoint combination the D0 term cancels exactly.
--
-- The remaining small assembly theorem is a certified O(B^4) comparison
-- between the ACTUAL marked determinant and this truncation.  Once paid, the
-- positive Q coefficient yields a nonempty punctured A-interval on which the
-- exact signed marked pole channel is strictly positive.
------------------------------------------------------------------------

data BidiMarkedPoleCurvatureCoordinate : Set where
  coshMarkedPrimeChannelZero :
    BidiMarkedPoleCurvatureCoordinate
  atomicMarkedPoleQuadraticEndpointSigns :
    BidiMarkedPoleCurvatureCoordinate
  atomicMarkedPoleQuadraticCorridorSigns :
    BidiMarkedPoleCurvatureCoordinate
  smoothMarkedPoleQuadraticEndpointSigns :
    BidiMarkedPoleCurvatureCoordinate
  strengthenedSmoothWitnessPositiveQuadraticCarrier :
    BidiMarkedPoleCurvatureCoordinate
  physicalMarkedPoleEqualsNormalizedDeterminant :
    BidiMarkedPoleCurvatureCoordinate
  exactQuadraticDeterminantTruncation :
    BidiMarkedPoleCurvatureCoordinate
  markedPairingFourthOrderRemainderBound :
    BidiMarkedPoleCurvatureCoordinate
  actualMarkedDeterminantFourthOrderRemainderBound :
    BidiMarkedPoleCurvatureCoordinate
  exactMarkedPolePositivePuncturedBand :
    BidiMarkedPoleCurvatureCoordinate
  markedPoleBiasCouplesToFourthAngularG3 :
    BidiMarkedPoleCurvatureCoordinate

bidiMarkedPoleCurvatureStatus :
  BidiMarkedPoleCurvatureCoordinate -> BidiMarkedFourthStatus
bidiMarkedPoleCurvatureStatus coshMarkedPrimeChannelZero = theoremOwned
bidiMarkedPoleCurvatureStatus atomicMarkedPoleQuadraticEndpointSigns =
  theoremOwned
bidiMarkedPoleCurvatureStatus atomicMarkedPoleQuadraticCorridorSigns =
  theoremOwned
bidiMarkedPoleCurvatureStatus smoothMarkedPoleQuadraticEndpointSigns =
  theoremOwned
bidiMarkedPoleCurvatureStatus
  strengthenedSmoothWitnessPositiveQuadraticCarrier =
  theoremOwned
bidiMarkedPoleCurvatureStatus physicalMarkedPoleEqualsNormalizedDeterminant =
  theoremOwned
bidiMarkedPoleCurvatureStatus exactQuadraticDeterminantTruncation =
  theoremOwned
bidiMarkedPoleCurvatureStatus markedPairingFourthOrderRemainderBound =
  theoremOwned
bidiMarkedPoleCurvatureStatus
  actualMarkedDeterminantFourthOrderRemainderBound =
  openAnalyticObstruction
bidiMarkedPoleCurvatureStatus exactMarkedPolePositivePuncturedBand =
  openAnalyticObstruction
bidiMarkedPoleCurvatureStatus markedPoleBiasCouplesToFourthAngularG3 =
  openAnalyticObstruction

markedPrimeChannelIsExactlyZero :
  bidiMarkedPoleCurvatureStatus coshMarkedPrimeChannelZero
    ≡ theoremOwned
markedPrimeChannelIsExactlyZero = refl

smoothMarkedPoleQuadraticSignalIsPaid :
  bidiMarkedPoleCurvatureStatus
    strengthenedSmoothWitnessPositiveQuadraticCarrier
    ≡ theoremOwned
smoothMarkedPoleQuadraticSignalIsPaid = refl

markedPairingRemainderIsPaid :
  bidiMarkedPoleCurvatureStatus markedPairingFourthOrderRemainderBound
    ≡ theoremOwned
markedPairingRemainderIsPaid = refl

actualMarkedPoleBandRemainsOpen :
  bidiMarkedPoleCurvatureStatus exactMarkedPolePositivePuncturedBand
    ≡ openAnalyticObstruction
actualMarkedPoleBandRemainsOpen = refl


------------------------------------------------------------------------
-- COMPLETE-JET STRICT-ABSORB RECUT (Lean donor)
--
-- Lean PR #22 moved the preferred terminal finite source bound from the older
-- joint-quartic remainder surface onto the already-owned COMPLETE quartic jet.
--
-- The leading local term is now literally
--
--   - S(W)/(6*(t/16)^6) * A4_local
--
-- and the residual debt is sixth order.  Consequently the obsolete positive
-- a^4 mass charge disappears from the preferred corrected-polarity budget.
--
-- The sixth debt is also scalarized against the same expanded literal zero
-- count used by H4, leaving the finite test in the form
--
--   scaled[
--     EV
--       + (3/2) r^2 N_expanded
--       - (2/5) r^5 muLower
--   ]
--   + sixthCoeff * N_expanded
--   + FarExact.
--
-- FarExact remains signed.  The only unpaid preferred item is the strict
-- comparison of that explicit scalar budget with compensationTargetThreshold.
--
-- This section is a donor/status receipt.  It does NOT claim an independent
-- Agda-native proof of the Lean analytic inequalities.
------------------------------------------------------------------------

data CompleteJetAbsorbCoordinate : Set where
  completeQuarticJetLeadingAngularIdentity : CompleteJetAbsorbCoordinate
  completeJetCorrectPolaritySourceBound : CompleteJetAbsorbCoordinate
  sixthDebtScalarEnvelope : CompleteJetAbsorbCoordinate
  sixthDebtExpandedWindowCountWeld : CompleteJetAbsorbCoordinate
  completeFiniteAbsorbBudget : CompleteJetAbsorbCoordinate
  strictCompleteScalarAbsorb : CompleteJetAbsorbCoordinate

completeJetAbsorbStatus :
  CompleteJetAbsorbCoordinate -> BidiMarkedFourthStatus
completeJetAbsorbStatus completeQuarticJetLeadingAngularIdentity =
  theoremOwned
completeJetAbsorbStatus completeJetCorrectPolaritySourceBound =
  theoremOwned
completeJetAbsorbStatus sixthDebtScalarEnvelope =
  theoremOwned
completeJetAbsorbStatus sixthDebtExpandedWindowCountWeld =
  theoremOwned
completeJetAbsorbStatus completeFiniteAbsorbBudget =
  theoremOwned
completeJetAbsorbStatus strictCompleteScalarAbsorb =
  openAnalyticObstruction

completeJetLeadingAngularIdentityPaid :
  completeJetAbsorbStatus completeQuarticJetLeadingAngularIdentity
    ≡ theoremOwned
completeJetLeadingAngularIdentityPaid = refl

completeJetSixthDebtScalarizationPaid :
  completeJetAbsorbStatus sixthDebtExpandedWindowCountWeld
    ≡ theoremOwned
completeJetSixthDebtScalarizationPaid = refl

strictCompleteScalarAbsorbRemainsOpen :
  completeJetAbsorbStatus strictCompleteScalarAbsorb
    ≡ openAnalyticObstruction
strictCompleteScalarAbsorbRemainsOpen = refl

completeJetAbsorbLeanDonorHead : String
completeJetAbsorbLeanDonorHead =
  "b4e13a85bdc71f217fd7648f238a08694849aedb"

completeJetAbsorbTransportedIntoAgdaKernelHere : Bool
completeJetAbsorbTransportedIntoAgdaKernelHere = false

completeJetAbsorbInterpretation : String
completeJetAbsorbInterpretation =
  "Preferred Clay-facing route: use the complete quartic jet, not the older wrong-polarity/fail-closed ABSORB candidate.  V4/H4 carrier work, explicit mu floor, complete-jet source orientation, and sixth-debt scalarization are Lean source-written donors.  The remaining preferred analytic wall is one strict scalar inequality comparing the exposed completeV4H4AbsorbBudgetAt against compensationTargetThreshold while retaining FarExact with sign."


------------------------------------------------------------------------
-- DIRECT STRICT-ABSORB -> G3 COMPILER DONOR
--
-- Lean PR #22 now compiles the preferred complete-jet scalar budget directly
-- through the already-owned cofinal exact-source limit and same-object tsum
-- weld into the literal completed G3 inequality.
--
-- Consequently there is no remaining preferred API/assembly seam between the
-- strict scalar test and G3.  The only open preferred proposition is the
-- eventual strict inequality
--
--   completeV4H4AbsorbBudgetAt EV n
--     <= compensationTargetThreshold rho - eps.
--
-- This remains a Lean donor/status receipt, not an Agda-native analytic proof.
------------------------------------------------------------------------

data CompleteJetAbsorbCompilerCoordinate : Set where
  completeStrictAbsorbFiniteSourceCompiler :
    CompleteJetAbsorbCompilerCoordinate
  completeStrictAbsorbCofinalGlobalCompiler :
    CompleteJetAbsorbCompilerCoordinate
  completeStrictAbsorbDirectG3Compiler :
    CompleteJetAbsorbCompilerCoordinate
  completeStrictScalarInequality :
    CompleteJetAbsorbCompilerCoordinate

completeJetAbsorbCompilerStatus :
  CompleteJetAbsorbCompilerCoordinate -> BidiMarkedFourthStatus
completeJetAbsorbCompilerStatus completeStrictAbsorbFiniteSourceCompiler =
  theoremOwned
completeJetAbsorbCompilerStatus completeStrictAbsorbCofinalGlobalCompiler =
  theoremOwned
completeJetAbsorbCompilerStatus completeStrictAbsorbDirectG3Compiler =
  theoremOwned
completeJetAbsorbCompilerStatus completeStrictScalarInequality =
  openAnalyticObstruction

completeStrictAbsorbDirectG3CompilerPaid :
  completeJetAbsorbCompilerStatus completeStrictAbsorbDirectG3Compiler
    ≡ theoremOwned
completeStrictAbsorbDirectG3CompilerPaid = refl

completeStrictScalarInequalityRemainsOpen :
  completeJetAbsorbCompilerStatus completeStrictScalarInequality
    ≡ openAnalyticObstruction
completeStrictScalarInequalityRemainsOpen = refl

completeJetDirectG3LeanDonorHead : String
completeJetDirectG3LeanDonorHead =
  "22dd5b83c5556cd11f28335a3477af49dd646e71"

completeJetDirectG3TransportedIntoAgdaKernelHere : Bool
completeJetDirectG3TransportedIntoAgdaKernelHere = false


------------------------------------------------------------------------
-- POST-SIXTH EIGHTH-ORDER SCALAR REMAINDER DONOR
--
-- Lean PR #22 certifies the degree-six Taylor remainder at eighth order:
--
--   |cos x  - (1 - x^2/2 + x^4/24 - x^6/720)| <= |x|^8 / 35840,
--   |cosh x - (1 + x^2/2 + x^4/24 + x^6/720)| <= |x|^8 / 35840,
--
-- for |x| <= 1.  Mixed joint lifting and literal r^-10 transport remain open.
------------------------------------------------------------------------

data PostSixthEighthOrderCoordinate : Set where
  scalarDegreeSixEighthRemainders : PostSixthEighthOrderCoordinate
  mixedJointDegreeSixEighthMajorant : PostSixthEighthOrderCoordinate
  literalFiniteBeyondSixthEighthBound : PostSixthEighthOrderCoordinate
  strictAbsorbAfterEighthSharpening : PostSixthEighthOrderCoordinate

postSixthEighthOrderStatus :
  PostSixthEighthOrderCoordinate -> BidiMarkedFourthStatus
postSixthEighthOrderStatus scalarDegreeSixEighthRemainders = theoremOwned
postSixthEighthOrderStatus mixedJointDegreeSixEighthMajorant =
  openAnalyticObstruction
postSixthEighthOrderStatus literalFiniteBeyondSixthEighthBound =
  openAnalyticObstruction
postSixthEighthOrderStatus strictAbsorbAfterEighthSharpening =
  openAnalyticObstruction

scalarEighthOrderTaylorDonorPaid :
  postSixthEighthOrderStatus scalarDegreeSixEighthRemainders ≡ theoremOwned
scalarEighthOrderTaylorDonorPaid = refl

postSixthEighthOrderLeanDonorHead : String
postSixthEighthOrderLeanDonorHead =
  "c24da874474457a7ac60f0f6df0a7ef1fc10807d"

postSixthEighthOrderTransportedIntoAgdaKernelHere : Bool
postSixthEighthOrderTransportedIntoAgdaKernelHere = false
