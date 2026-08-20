module DASHI.Moonshine.P37MarkedX2DeckTorsorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Identify the 18 explicit Deuring lambda roots at p=37 with the source-native
-- full-level-2 carrier
--
--   P37GeometricJ x Frame6.
--
-- Each of the three coarse supersingular classes has a regular six-frame S3
-- torsor.  The frame table is bridged to the existing Level2Frame presentation
-- already used at p=11, so its right deck generators and S3 laws are reused
-- rather than duplicated.
--
-- The chart is the exact one independently verified by
-- scripts/verify_p37_legendre_marked_hecke.py from the anharmonic actions
--
--   r(lambda)=1/(1-lambda),  s(lambda)=1-lambda.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root3
import DASHI.Moonshine.P11FullLevel2RigidificationExact as Level2
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37

------------------------------------------------------------------------
-- Exact Frame6 <-> existing regular S3 frame chart.
------------------------------------------------------------------------

frameToLevel2 : P37.Frame6 → Level2.Level2Frame
frameToLevel2 P37.frame0 = Level2.f0
frameToLevel2 P37.frame1 = Level2.f1
frameToLevel2 P37.frame2 = Level2.f2
frameToLevel2 P37.frame3 = Level2.f3
frameToLevel2 P37.frame4 = Level2.f4
frameToLevel2 P37.frame5 = Level2.f5

level2ToFrame : Level2.Level2Frame → P37.Frame6
level2ToFrame Level2.f0 = P37.frame0
level2ToFrame Level2.f1 = P37.frame1
level2ToFrame Level2.f2 = P37.frame2
level2ToFrame Level2.f3 = P37.frame3
level2ToFrame Level2.f4 = P37.frame4
level2ToFrame Level2.f5 = P37.frame5

frameAfterLevel2 : (f : Level2.Level2Frame) → frameToLevel2 (level2ToFrame f) ≡ f
frameAfterLevel2 Level2.f0 = refl
frameAfterLevel2 Level2.f1 = refl
frameAfterLevel2 Level2.f2 = refl
frameAfterLevel2 Level2.f3 = refl
frameAfterLevel2 Level2.f4 = refl
frameAfterLevel2 Level2.f5 = refl

level2AfterFrame : (f : P37.Frame6) → level2ToFrame (frameToLevel2 f) ≡ f
level2AfterFrame P37.frame0 = refl
level2AfterFrame P37.frame1 = refl
level2AfterFrame P37.frame2 = refl
level2AfterFrame P37.frame3 = refl
level2AfterFrame P37.frame4 = refl
level2AfterFrame P37.frame5 = refl

rightR37 : P37.Frame6 → P37.Frame6
rightR37 f = level2ToFrame (Deck.rightR (frameToLevel2 f))

rightS37 : P37.Frame6 → P37.Frame6
rightS37 f = level2ToFrame (Deck.rightS (frameToLevel2 f))

rightR37Three : (f : P37.Frame6) → rightR37 (rightR37 (rightR37 f)) ≡ f
rightR37Three P37.frame0 = refl
rightR37Three P37.frame1 = refl
rightR37Three P37.frame2 = refl
rightR37Three P37.frame3 = refl
rightR37Three P37.frame4 = refl
rightR37Three P37.frame5 = refl

rightS37Two : (f : P37.Frame6) → rightS37 (rightS37 f) ≡ f
rightS37Two P37.frame0 = refl
rightS37Two P37.frame1 = refl
rightS37Two P37.frame2 = refl
rightS37Two P37.frame3 = refl
rightS37Two P37.frame4 = refl
rightS37Two P37.frame5 = refl

rightSRS37 :
  (f : P37.Frame6) →
  rightS37 (rightR37 (rightS37 f)) ≡ rightR37 (rightR37 f)
rightSRS37 P37.frame0 = refl
rightSRS37 P37.frame1 = refl
rightSRS37 P37.frame2 = refl
rightSRS37 P37.frame3 = refl
rightSRS37 P37.frame4 = refl
rightSRS37 P37.frame5 = refl

------------------------------------------------------------------------
-- Explicit lambda-root <-> coarse-class x frame chart.
------------------------------------------------------------------------

lambdaToFullLevel2 : P37.P37SupersingularLambda → P37.P37FullLevel2Point
lambdaToFullLevel2 (P37.lambda37 P37.q0 P37.root0) = P37.p37MarkedPoint P37.jConjugate0 P37.frame0
lambdaToFullLevel2 (P37.lambda37 P37.q0 P37.root1) = P37.p37MarkedPoint P37.jConjugate1 P37.frame0
lambdaToFullLevel2 (P37.lambda37 P37.q1 P37.root0) = P37.p37MarkedPoint P37.j8 P37.frame0
lambdaToFullLevel2 (P37.lambda37 P37.q1 P37.root1) = P37.p37MarkedPoint P37.j8 P37.frame4
lambdaToFullLevel2 (P37.lambda37 P37.q2 P37.root0) = P37.p37MarkedPoint P37.jConjugate1 P37.frame2
lambdaToFullLevel2 (P37.lambda37 P37.q2 P37.root1) = P37.p37MarkedPoint P37.jConjugate0 P37.frame2
lambdaToFullLevel2 (P37.lambda37 P37.q3 P37.root0) = P37.p37MarkedPoint P37.jConjugate1 P37.frame1
lambdaToFullLevel2 (P37.lambda37 P37.q3 P37.root1) = P37.p37MarkedPoint P37.jConjugate0 P37.frame1
lambdaToFullLevel2 (P37.lambda37 P37.q4 P37.root0) = P37.p37MarkedPoint P37.jConjugate0 P37.frame4
lambdaToFullLevel2 (P37.lambda37 P37.q4 P37.root1) = P37.p37MarkedPoint P37.jConjugate1 P37.frame4
lambdaToFullLevel2 (P37.lambda37 P37.q5 P37.root0) = P37.p37MarkedPoint P37.jConjugate0 P37.frame5
lambdaToFullLevel2 (P37.lambda37 P37.q5 P37.root1) = P37.p37MarkedPoint P37.jConjugate1 P37.frame5
lambdaToFullLevel2 (P37.lambda37 P37.q6 P37.root0) = P37.p37MarkedPoint P37.j8 P37.frame1
lambdaToFullLevel2 (P37.lambda37 P37.q6 P37.root1) = P37.p37MarkedPoint P37.j8 P37.frame3
lambdaToFullLevel2 (P37.lambda37 P37.q7 P37.root0) = P37.p37MarkedPoint P37.jConjugate1 P37.frame3
lambdaToFullLevel2 (P37.lambda37 P37.q7 P37.root1) = P37.p37MarkedPoint P37.jConjugate0 P37.frame3
lambdaToFullLevel2 (P37.lambda37 P37.q8 P37.root0) = P37.p37MarkedPoint P37.j8 P37.frame5
lambdaToFullLevel2 (P37.lambda37 P37.q8 P37.root1) = P37.p37MarkedPoint P37.j8 P37.frame2

fullLevel2ToLambda : P37.P37FullLevel2Point → P37.P37SupersingularLambda
fullLevel2ToLambda (P37.p37MarkedPoint P37.j8 P37.frame0) = P37.lambda37 P37.q1 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.j8 P37.frame1) = P37.lambda37 P37.q6 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.j8 P37.frame2) = P37.lambda37 P37.q8 P37.root1
fullLevel2ToLambda (P37.p37MarkedPoint P37.j8 P37.frame3) = P37.lambda37 P37.q6 P37.root1
fullLevel2ToLambda (P37.p37MarkedPoint P37.j8 P37.frame4) = P37.lambda37 P37.q1 P37.root1
fullLevel2ToLambda (P37.p37MarkedPoint P37.j8 P37.frame5) = P37.lambda37 P37.q8 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate0 P37.frame0) = P37.lambda37 P37.q0 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate0 P37.frame1) = P37.lambda37 P37.q3 P37.root1
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate0 P37.frame2) = P37.lambda37 P37.q2 P37.root1
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate0 P37.frame3) = P37.lambda37 P37.q7 P37.root1
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate0 P37.frame4) = P37.lambda37 P37.q4 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate0 P37.frame5) = P37.lambda37 P37.q5 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate1 P37.frame0) = P37.lambda37 P37.q0 P37.root1
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate1 P37.frame1) = P37.lambda37 P37.q3 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate1 P37.frame2) = P37.lambda37 P37.q2 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate1 P37.frame3) = P37.lambda37 P37.q7 P37.root0
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate1 P37.frame4) = P37.lambda37 P37.q4 P37.root1
fullLevel2ToLambda (P37.p37MarkedPoint P37.jConjugate1 P37.frame5) = P37.lambda37 P37.q5 P37.root1

lambdaChartRoundTrip :
  (x : P37.P37SupersingularLambda) → fullLevel2ToLambda (lambdaToFullLevel2 x) ≡ x
lambdaChartRoundTrip (P37.lambda37 P37.q0 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q0 P37.root1) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q1 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q1 P37.root1) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q2 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q2 P37.root1) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q3 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q3 P37.root1) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q4 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q4 P37.root1) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q5 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q5 P37.root1) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q6 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q6 P37.root1) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q7 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q7 P37.root1) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q8 P37.root0) = refl
lambdaChartRoundTrip (P37.lambda37 P37.q8 P37.root1) = refl

fullLevel2ChartRoundTrip :
  (x : P37.P37FullLevel2Point) → lambdaToFullLevel2 (fullLevel2ToLambda x) ≡ x
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.j8 P37.frame0) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.j8 P37.frame1) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.j8 P37.frame2) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.j8 P37.frame3) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.j8 P37.frame4) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.j8 P37.frame5) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate0 P37.frame0) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate0 P37.frame1) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate0 P37.frame2) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate0 P37.frame3) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate0 P37.frame4) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate0 P37.frame5) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate1 P37.frame0) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate1 P37.frame1) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate1 P37.frame2) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate1 P37.frame3) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate1 P37.frame4) = refl
fullLevel2ChartRoundTrip (P37.p37MarkedPoint P37.jConjugate1 P37.frame5) = refl

------------------------------------------------------------------------
-- Right deck S3 transported to the actual Deuring-root carrier.
------------------------------------------------------------------------

rightRPoint : P37.P37FullLevel2Point → P37.P37FullLevel2Point
rightRPoint (P37.p37MarkedPoint j frame) = P37.p37MarkedPoint j (rightR37 frame)

rightSPoint : P37.P37FullLevel2Point → P37.P37FullLevel2Point
rightSPoint (P37.p37MarkedPoint j frame) = P37.p37MarkedPoint j (rightS37 frame)

lambdaDeckR : P37.P37SupersingularLambda → P37.P37SupersingularLambda
lambdaDeckR x = fullLevel2ToLambda (rightRPoint (lambdaToFullLevel2 x))

lambdaDeckS : P37.P37SupersingularLambda → P37.P37SupersingularLambda
lambdaDeckS x = fullLevel2ToLambda (rightSPoint (lambdaToFullLevel2 x))

lambdaDeckRThree :
  (x : P37.P37SupersingularLambda) →
  lambdaDeckR (lambdaDeckR (lambdaDeckR x)) ≡ x
lambdaDeckRThree (P37.lambda37 P37.q0 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q0 P37.root1) = refl
lambdaDeckRThree (P37.lambda37 P37.q1 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q1 P37.root1) = refl
lambdaDeckRThree (P37.lambda37 P37.q2 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q2 P37.root1) = refl
lambdaDeckRThree (P37.lambda37 P37.q3 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q3 P37.root1) = refl
lambdaDeckRThree (P37.lambda37 P37.q4 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q4 P37.root1) = refl
lambdaDeckRThree (P37.lambda37 P37.q5 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q5 P37.root1) = refl
lambdaDeckRThree (P37.lambda37 P37.q6 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q6 P37.root1) = refl
lambdaDeckRThree (P37.lambda37 P37.q7 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q7 P37.root1) = refl
lambdaDeckRThree (P37.lambda37 P37.q8 P37.root0) = refl
lambdaDeckRThree (P37.lambda37 P37.q8 P37.root1) = refl

lambdaDeckSTwo :
  (x : P37.P37SupersingularLambda) → lambdaDeckS (lambdaDeckS x) ≡ x
lambdaDeckSTwo (P37.lambda37 P37.q0 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q0 P37.root1) = refl
lambdaDeckSTwo (P37.lambda37 P37.q1 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q1 P37.root1) = refl
lambdaDeckSTwo (P37.lambda37 P37.q2 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q2 P37.root1) = refl
lambdaDeckSTwo (P37.lambda37 P37.q3 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q3 P37.root1) = refl
lambdaDeckSTwo (P37.lambda37 P37.q4 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q4 P37.root1) = refl
lambdaDeckSTwo (P37.lambda37 P37.q5 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q5 P37.root1) = refl
lambdaDeckSTwo (P37.lambda37 P37.q6 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q6 P37.root1) = refl
lambdaDeckSTwo (P37.lambda37 P37.q7 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q7 P37.root1) = refl
lambdaDeckSTwo (P37.lambda37 P37.q8 P37.root0) = refl
lambdaDeckSTwo (P37.lambda37 P37.q8 P37.root1) = refl

lambdaDeckSRS :
  (x : P37.P37SupersingularLambda) →
  lambdaDeckS (lambdaDeckR (lambdaDeckS x))
  ≡ lambdaDeckR (lambdaDeckR x)
lambdaDeckSRS (P37.lambda37 P37.q0 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q0 P37.root1) = refl
lambdaDeckSRS (P37.lambda37 P37.q1 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q1 P37.root1) = refl
lambdaDeckSRS (P37.lambda37 P37.q2 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q2 P37.root1) = refl
lambdaDeckSRS (P37.lambda37 P37.q3 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q3 P37.root1) = refl
lambdaDeckSRS (P37.lambda37 P37.q4 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q4 P37.root1) = refl
lambdaDeckSRS (P37.lambda37 P37.q5 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q5 P37.root1) = refl
lambdaDeckSRS (P37.lambda37 P37.q6 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q6 P37.root1) = refl
lambdaDeckSRS (P37.lambda37 P37.q7 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q7 P37.root1) = refl
lambdaDeckSRS (P37.lambda37 P37.q8 P37.root0) = refl
lambdaDeckSRS (P37.lambda37 P37.q8 P37.root1) = refl

------------------------------------------------------------------------
-- C3 character coordinates on each of the two deck-R cycles per coarse fibre.
------------------------------------------------------------------------

data FrameCycle : Set where
  cycle0 cycle1 : FrameCycle

frameCycle : P37.Frame6 → FrameCycle
frameCycle P37.frame0 = cycle0
frameCycle P37.frame1 = cycle0
frameCycle P37.frame2 = cycle0
frameCycle P37.frame3 = cycle1
frameCycle P37.frame4 = cycle1
frameCycle P37.frame5 = cycle1

framePhase : P37.Frame6 → Phase.Phase3
framePhase P37.frame0 = Phase.phase0
framePhase P37.frame1 = Phase.phase1
framePhase P37.frame2 = Phase.phase2
framePhase P37.frame3 = Phase.phase0
framePhase P37.frame5 = Phase.phase1
framePhase P37.frame4 = Phase.phase2

rightRRotatesFramePhase :
  (f : P37.Frame6) → framePhase (rightR37 f) ≡ Root3.zetaRotate (framePhase f)
rightRRotatesFramePhase P37.frame0 = refl
rightRRotatesFramePhase P37.frame1 = refl
rightRRotatesFramePhase P37.frame2 = refl
rightRRotatesFramePhase P37.frame3 = refl
rightRRotatesFramePhase P37.frame4 = refl
rightRRotatesFramePhase P37.frame5 = refl

rightSSwapsCycle :
  (f : P37.Frame6) →
  frameCycle (rightS37 f) ≡
    (case frameCycle f of λ where
      cycle0 → cycle1
      cycle1 → cycle0)
rightSSwapsCycle P37.frame0 = refl
rightSSwapsCycle P37.frame1 = refl
rightSSwapsCycle P37.frame2 = refl
rightSSwapsCycle P37.frame3 = refl
rightSSwapsCycle P37.frame4 = refl
rightSSwapsCycle P37.frame5 = refl

rightSConjugatesFramePhase :
  (f : P37.Frame6) →
  framePhase (rightS37 f) ≡ Root3.phaseInverse (framePhase f)
rightSConjugatesFramePhase P37.frame0 = refl
rightSConjugatesFramePhase P37.frame1 = refl
rightSConjugatesFramePhase P37.frame2 = refl
rightSConjugatesFramePhase P37.frame3 = refl
rightSConjugatesFramePhase P37.frame4 = refl
rightSConjugatesFramePhase P37.frame5 = refl

frameCharacter : Phase.Phase3 → P37.Frame6 → Phase.Phase3
frameCharacter k frame = Root3.character k (framePhase frame)

frameCharacterDiagonalizesRightR :
  (k : Phase.Phase3) → (frame : P37.Frame6) →
  frameCharacter k (rightR37 frame)
  ≡ Root3.phaseMul k (frameCharacter k frame)
frameCharacterDiagonalizesRightR Phase.phase0 P37.frame0 = refl
frameCharacterDiagonalizesRightR Phase.phase0 P37.frame1 = refl
frameCharacterDiagonalizesRightR Phase.phase0 P37.frame2 = refl
frameCharacterDiagonalizesRightR Phase.phase0 P37.frame3 = refl
frameCharacterDiagonalizesRightR Phase.phase0 P37.frame4 = refl
frameCharacterDiagonalizesRightR Phase.phase0 P37.frame5 = refl
frameCharacterDiagonalizesRightR Phase.phase1 P37.frame0 = refl
frameCharacterDiagonalizesRightR Phase.phase1 P37.frame1 = refl
frameCharacterDiagonalizesRightR Phase.phase1 P37.frame2 = refl
frameCharacterDiagonalizesRightR Phase.phase1 P37.frame3 = refl
frameCharacterDiagonalizesRightR Phase.phase1 P37.frame4 = refl
frameCharacterDiagonalizesRightR Phase.phase1 P37.frame5 = refl
frameCharacterDiagonalizesRightR Phase.phase2 P37.frame0 = refl
frameCharacterDiagonalizesRightR Phase.phase2 P37.frame1 = refl
frameCharacterDiagonalizesRightR Phase.phase2 P37.frame2 = refl
frameCharacterDiagonalizesRightR Phase.phase2 P37.frame3 = refl
frameCharacterDiagonalizesRightR Phase.phase2 P37.frame4 = refl
frameCharacterDiagonalizesRightR Phase.phase2 P37.frame5 = refl

record P37MarkedX2DeckTorsorBoundary : Set where
  field
    deuringRootsToThreeBySixChartConstructed : Bool
    deuringRootsToThreeBySixChartConstructedIsTrue :
      deuringRootsToThreeBySixChartConstructed ≡ true

    existingS3FramePresentationReused : Bool
    existingS3FramePresentationReusedIsTrue :
      existingS3FramePresentationReused ≡ true

    exactDeckS3OnLambdaCarrierConstructed : Bool
    exactDeckS3OnLambdaCarrierConstructedIsTrue :
      exactDeckS3OnLambdaCarrierConstructed ≡ true

    phase3CharactersDiagonalizeEachDeckC3Cycle : Bool
    phase3CharactersDiagonalizeEachDeckC3CycleIsTrue :
      phase3CharactersDiagonalizeEachDeckC3Cycle ≡ true

canonicalP37MarkedX2DeckTorsorBoundary : P37MarkedX2DeckTorsorBoundary
canonicalP37MarkedX2DeckTorsorBoundary = record
  { deuringRootsToThreeBySixChartConstructed = true
  ; deuringRootsToThreeBySixChartConstructedIsTrue = refl
  ; existingS3FramePresentationReused = true
  ; existingS3FramePresentationReusedIsTrue = refl
  ; exactDeckS3OnLambdaCarrierConstructed = true
  ; exactDeckS3OnLambdaCarrierConstructedIsTrue = refl
  ; phase3CharactersDiagonalizeEachDeckC3Cycle = true
  ; phase3CharactersDiagonalizeEachDeckC3CycleIsTrue = refl
  }
