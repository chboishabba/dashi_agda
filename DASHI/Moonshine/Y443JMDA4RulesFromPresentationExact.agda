module DASHI.Moonshine.Y443JMDA4RulesFromPresentationExact where

------------------------------------------------------------------------
-- SOURCE-ONLY CLOSURE OF JMD BETA ORDER FIVE.
--
-- The actual 80 Y443 relation words, and nothing else, provide:
-- 4 node-square relations on x5..x8;
-- 3 m=2 nonadjacent-pair relations;
-- 3 m=3 adjacent-pair relations.
--
-- Consequences are wired into the previous general group-theoretic
-- semantic Coxeter rules. The 35-step finite Agda rewriting machine
-- then proves beta^5=1 IN THAT SAME SELECTED GROUP.
--
-- This completes the JMD beta power lemma from original source
-- presentation with no standalone "beta order five" hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMD
import DASHI.Moonshine.Y443JMDBetaFiveFiniteRewriteExact as W
import DASHI.Moonshine.Y443JMDBetaFiveSemanticCompilerExact as Sem
import DASHI.Moonshine.Y443CoxeterRelatorSemanticLawsExact as Laws
import DASHI.Moonshine.Y443JMDNonadjacentRelatorConsequencesExact as Relations
import DASHI.Moonshine.Y443JMDFromRelatorsToPowerExact as PowerRoute
import DASHI.Moonshine.Y443JMDConcretePairPowerCompilerExact as Compiler
import DASHI.Moonshine.Y443JMDTracePowerExact as Power
import DASHI.Moonshine.TwistedModuleModularity as TM

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

------------------------------------------------------------------------
-- Original exact relator indices in the SAME 80-word enumeration:
-- beta x5..x8 squares at indexes 5..8;
-- b2c2=57, b2d2=58, b2e2=59,
-- c2d2=63, c2e2=64, d2e2=68 (all zero-based).
------------------------------------------------------------------------

memberb2c2 : Relations._∈_
    (Y.pairRelator (Y.pair Y.b2 Y.c2)) Y.monsterRelators
memberb2c2 = Relations.there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (Relations.here)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

memberb2d2 : Relations._∈_
    (Y.pairRelator (Y.pair Y.b2 Y.d2)) Y.monsterRelators
memberb2d2 = Relations.there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (Relations.here))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

memberb2e2 : Relations._∈_
    (Y.pairRelator (Y.pair Y.b2 Y.e2)) Y.monsterRelators
memberb2e2 = Relations.there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (Relations.here)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

memberc2d2 : Relations._∈_
    (Y.pairRelator (Y.pair Y.c2 Y.d2)) Y.monsterRelators
memberc2d2 = Relations.there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (Relations.here)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

memberc2e2 : Relations._∈_
    (Y.pairRelator (Y.pair Y.c2 Y.e2)) Y.monsterRelators
memberc2e2 = Relations.there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (Relations.here))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

memberd2e2 : Relations._∈_
    (Y.pairRelator (Y.pair Y.d2 Y.e2)) Y.monsterRelators
memberd2e2 = Relations.there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (Relations.here))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


module Actual {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G)
  (all : Pair.RelatorsSatisfied gi nodes Y.monsterRelators) where

  module R = Relations.SourceConsequences gi nodes all
  module L = Laws.Laws gi nodes all

  squareAllowed :
    (a b : W.Gen) →
    W.eqG a b ≡ true →
    Pair.multiply gi (nodes (Sem.sourceGen a))
      (nodes (Sem.sourceGen b)) ≡ Pair.identity gi
  squareAllowed W.x5 W.x5 proof = R.squareFrom Y.b2 Relations.memberSquareb2
  squareAllowed W.x5 W.x6 ()
  squareAllowed W.x5 W.x7 ()
  squareAllowed W.x5 W.x8 ()
  squareAllowed W.x6 W.x5 ()
  squareAllowed W.x6 W.x6 proof = R.squareFrom Y.c2 Relations.memberSquarec2
  squareAllowed W.x6 W.x7 ()
  squareAllowed W.x6 W.x8 ()
  squareAllowed W.x7 W.x5 ()
  squareAllowed W.x7 W.x6 ()
  squareAllowed W.x7 W.x7 proof = R.squareFrom Y.d2 Relations.memberSquared2
  squareAllowed W.x7 W.x8 ()
  squareAllowed W.x8 W.x5 ()
  squareAllowed W.x8 W.x6 ()
  squareAllowed W.x8 W.x7 ()
  squareAllowed W.x8 W.x8 proof = R.squareFrom Y.e2 Relations.memberSquaree2

  commuteAllowed :
    (a b : W.Gen) →
    W.canCommute a b ≡ true →
    Pair.multiply gi (nodes (Sem.sourceGen a))
      (nodes (Sem.sourceGen b)) ≡
    Pair.multiply gi (nodes (Sem.sourceGen b))
      (nodes (Sem.sourceGen a))
  commuteAllowed W.x5 W.x5 ()
  commuteAllowed W.x5 W.x6 ()
  commuteAllowed W.x5 W.x7 proof =
    R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.d2)
      (R.squareFrom Y.b2 Relations.memberSquareb2)
      (R.squareFrom Y.d2 Relations.memberSquared2)
      (R.nonedgeProductSquare Y.b2 Y.d2 memberb2d2 refl)
  commuteAllowed W.x5 W.x8 proof =
    R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.e2)
      (R.squareFrom Y.b2 Relations.memberSquareb2)
      (R.squareFrom Y.e2 Relations.memberSquaree2)
      (R.nonedgeProductSquare Y.b2 Y.e2 memberb2e2 refl)
  commuteAllowed W.x6 W.x5 ()
  commuteAllowed W.x6 W.x6 ()
  commuteAllowed W.x6 W.x7 ()
  commuteAllowed W.x6 W.x8 proof =
    R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.e2)
      (R.squareFrom Y.c2 Relations.memberSquarec2)
      (R.squareFrom Y.e2 Relations.memberSquaree2)
      (R.nonedgeProductSquare Y.c2 Y.e2 memberc2e2 refl)
  commuteAllowed W.x7 W.x5 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.d2)
      (R.squareFrom Y.b2 Relations.memberSquareb2)
      (R.squareFrom Y.d2 Relations.memberSquared2)
      (R.nonedgeProductSquare Y.b2 Y.d2 memberb2d2 refl))
  commuteAllowed W.x7 W.x6 ()
  commuteAllowed W.x7 W.x7 ()
  commuteAllowed W.x7 W.x8 ()
  commuteAllowed W.x8 W.x5 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.e2)
      (R.squareFrom Y.b2 Relations.memberSquareb2)
      (R.squareFrom Y.e2 Relations.memberSquaree2)
      (R.nonedgeProductSquare Y.b2 Y.e2 memberb2e2 refl))
  commuteAllowed W.x8 W.x6 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.e2)
      (R.squareFrom Y.c2 Relations.memberSquarec2)
      (R.squareFrom Y.e2 Relations.memberSquaree2)
      (R.nonedgeProductSquare Y.c2 Y.e2 memberc2e2 refl))
  commuteAllowed W.x8 W.x7 ()
  commuteAllowed W.x8 W.x8 ()

  braidAllowed :
    (a b c : W.Gen) →
    W.canBraid a b c ≡ true →
    Pair.multiply gi (nodes (Sem.sourceGen a))
      (Pair.multiply gi (nodes (Sem.sourceGen b))
        (nodes (Sem.sourceGen c))) ≡
    Pair.multiply gi (nodes (Sem.sourceGen b))
      (Pair.multiply gi (nodes (Sem.sourceGen a))
        (nodes (Sem.sourceGen b)))
  braidAllowed W.x5 W.x5 W.x5 ()
  braidAllowed W.x5 W.x5 W.x6 ()
  braidAllowed W.x5 W.x5 W.x7 ()
  braidAllowed W.x5 W.x5 W.x8 ()
  braidAllowed W.x5 W.x6 W.x5 proof =
    L.edgeBraid Y.b2 Y.c2
      memberb2c2
      Relations.memberSquareb2
      Relations.memberSquarec2 refl
  braidAllowed W.x5 W.x6 W.x6 ()
  braidAllowed W.x5 W.x6 W.x7 ()
  braidAllowed W.x5 W.x6 W.x8 ()
  braidAllowed W.x5 W.x7 W.x5 ()
  braidAllowed W.x5 W.x7 W.x6 ()
  braidAllowed W.x5 W.x7 W.x7 ()
  braidAllowed W.x5 W.x7 W.x8 ()
  braidAllowed W.x5 W.x8 W.x5 ()
  braidAllowed W.x5 W.x8 W.x6 ()
  braidAllowed W.x5 W.x8 W.x7 ()
  braidAllowed W.x5 W.x8 W.x8 ()
  braidAllowed W.x6 W.x5 W.x5 ()
  braidAllowed W.x6 W.x5 W.x6 proof =
    sym (L.edgeBraid Y.b2 Y.c2
      memberb2c2
      Relations.memberSquareb2
      Relations.memberSquarec2 refl)
  braidAllowed W.x6 W.x5 W.x7 ()
  braidAllowed W.x6 W.x5 W.x8 ()
  braidAllowed W.x6 W.x6 W.x5 ()
  braidAllowed W.x6 W.x6 W.x6 ()
  braidAllowed W.x6 W.x6 W.x7 ()
  braidAllowed W.x6 W.x6 W.x8 ()
  braidAllowed W.x6 W.x7 W.x5 ()
  braidAllowed W.x6 W.x7 W.x6 proof =
    L.edgeBraid Y.c2 Y.d2
      memberc2d2
      Relations.memberSquarec2
      Relations.memberSquared2 refl
  braidAllowed W.x6 W.x7 W.x7 ()
  braidAllowed W.x6 W.x7 W.x8 ()
  braidAllowed W.x6 W.x8 W.x5 ()
  braidAllowed W.x6 W.x8 W.x6 ()
  braidAllowed W.x6 W.x8 W.x7 ()
  braidAllowed W.x6 W.x8 W.x8 ()
  braidAllowed W.x7 W.x5 W.x5 ()
  braidAllowed W.x7 W.x5 W.x6 ()
  braidAllowed W.x7 W.x5 W.x7 ()
  braidAllowed W.x7 W.x5 W.x8 ()
  braidAllowed W.x7 W.x6 W.x5 ()
  braidAllowed W.x7 W.x6 W.x6 ()
  braidAllowed W.x7 W.x6 W.x7 proof =
    sym (L.edgeBraid Y.c2 Y.d2
      memberc2d2
      Relations.memberSquarec2
      Relations.memberSquared2 refl)
  braidAllowed W.x7 W.x6 W.x8 ()
  braidAllowed W.x7 W.x7 W.x5 ()
  braidAllowed W.x7 W.x7 W.x6 ()
  braidAllowed W.x7 W.x7 W.x7 ()
  braidAllowed W.x7 W.x7 W.x8 ()
  braidAllowed W.x7 W.x8 W.x5 ()
  braidAllowed W.x7 W.x8 W.x6 ()
  braidAllowed W.x7 W.x8 W.x7 proof =
    L.edgeBraid Y.d2 Y.e2
      memberd2e2
      Relations.memberSquared2
      Relations.memberSquaree2 refl
  braidAllowed W.x7 W.x8 W.x8 ()
  braidAllowed W.x8 W.x5 W.x5 ()
  braidAllowed W.x8 W.x5 W.x6 ()
  braidAllowed W.x8 W.x5 W.x7 ()
  braidAllowed W.x8 W.x5 W.x8 ()
  braidAllowed W.x8 W.x6 W.x5 ()
  braidAllowed W.x8 W.x6 W.x6 ()
  braidAllowed W.x8 W.x6 W.x7 ()
  braidAllowed W.x8 W.x6 W.x8 ()
  braidAllowed W.x8 W.x7 W.x5 ()
  braidAllowed W.x8 W.x7 W.x6 ()
  braidAllowed W.x8 W.x7 W.x7 ()
  braidAllowed W.x8 W.x7 W.x8 proof =
    sym (L.edgeBraid Y.d2 Y.e2
      memberd2e2
      Relations.memberSquared2
      Relations.memberSquaree2 refl)
  braidAllowed W.x8 W.x8 W.x5 ()
  braidAllowed W.x8 W.x8 W.x6 ()
  braidAllowed W.x8 W.x8 W.x7 ()
  braidAllowed W.x8 W.x8 W.x8 ()

  actualRules : Sem.CoxeterA4LocalRules gi nodes
  actualRules = record
    { Sem.squareWhenAllowed = squareAllowed
    ; Sem.commuteWhenAllowed = commuteAllowed
    ; Sem.braidWhenAllowed = braidAllowed
    }

  betaFiveFromOriginal80Relators :
    Power.groupPower gi (JMD.betaElement gi nodes) 5 ≡ Pair.identity gi
  betaFiveFromOriginal80Relators =
    Sem.Semantic.betaOrderFiveFromFiniteCertificate
      gi nodes actualRules

  x4InPairWithNoExtraPowerPremise :
    Pair.RepresentedByPair gi
      (JMD.uElement gi nodes) (JMD.vElement gi nodes)
      (nodes JMD.x4)
  x4InPairWithNoExtraPowerPremise =
    PowerRoute.x4InJMDPairFromActualRelators gi nodes all
      record { PowerRoute.fifthPower = betaFiveFromOriginal80Relators }

  betaInPairWithNoExtraPowerPremise :
    Pair.RepresentedByPair gi
      (JMD.uElement gi nodes) (JMD.vElement gi nodes)
      (JMD.betaElement gi nodes)
  betaInPairWithNoExtraPowerPremise =
    PowerRoute.betaInJMDPairFromActualRelators gi nodes all
      record { PowerRoute.fifthPower = betaFiveFromOriginal80Relators }
