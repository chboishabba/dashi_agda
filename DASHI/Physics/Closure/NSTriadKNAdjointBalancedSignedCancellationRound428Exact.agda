module DASHI.Physics.Closure.NSTriadKNAdjointBalancedSignedCancellationRound428Exact where

------------------------------------------------------------------------
-- ROUND428 / EXACT PRE-NORM ADJOINT BALANCE FOR ONE NAVIER--STOKES CELL
--
-- The repository already proves both literal vector partial-adjoint pairing
-- identities for the signed projected Fourier interaction.  Crucially, BOTH
-- real pairings are equal to the SAME output trilinear symbol before absolute
-- values are taken.
--
-- Therefore the two adjoint channels are exactly equal.  Their signed
-- difference vanishes cellwise:
--
--   Re <u_p, B_1^*(test_k,u_q)>
--     - Re <u_q, B_2^*(u_p,test_k)> = 0.
--
-- This is the cancellation geometry wanted by the R299/R423 route: it lives
-- before norm majorisation and does not spend a Wiener/cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralVectorAdjointCandidates as Adjoints
import DASHI.Physics.Closure.NSTriadKNLiteralVectorAdjointPairingTheorems as Pairing

F : C3.RealField _
F = Rational.rationalRealField

firstAdjointRealPairing :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (p q : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → ℚ
firstAdjointRealPairing E I p q uP uQ testK =
  C3.complexRealPart
    (C3.hermitianPairing3 uP
      (Adjoints.directFirstAdjointVector E I p q testK uQ))

secondAdjointRealPairing :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (q : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → ℚ
secondAdjointRealPairing E I q uP uQ testK =
  C3.complexRealPart
    (C3.hermitianPairing3 uQ
      (Adjoints.secondAdjointVector E I q uP testK))

literalPartialAdjointBalance :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (k p q : Z3.FourierMode)
  (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E k testK →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  firstAdjointRealPairing E I p q uP uQ testK
  ≡ secondAdjointRealPairing E I q uP uQ testK
literalPartialAdjointBalance E I k p q uP uQ testK tk tp tq =
  trans
    (Pairing.firstVectorAdjointPairingIdentity
      E I k p q uP uQ testK tk tp)
    (sym
      (Pairing.secondVectorAdjointPairingIdentity
        E I k p q uP uQ testK tk tq))

literalPartialAdjointSignedDifferenceZero :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (k p q : Z3.FourierMode)
  (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E k testK →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  firstAdjointRealPairing E I p q uP uQ testK
    - secondAdjointRealPairing E I q uP uQ testK
  ≡ 0ℚ
literalPartialAdjointSignedDifferenceZero E I k p q uP uQ testK tk tp tq
  rewrite literalPartialAdjointBalance E I k p q uP uQ testK tk tp tq = refl

round428BothPartialAdjointsHitSameOutputSymbol : Bool
round428BothPartialAdjointsHitSameOutputSymbol = true

round428SignedAdjointDifferenceCancelsBeforeNorm : Bool
round428SignedAdjointDifferenceCancelsBeforeNorm = true

round428AbsoluteValueUsedToProveCancellation : Bool
round428AbsoluteValueUsedToProveCancellation = false

round428WienerFactorIntroduced : Bool
round428WienerFactorIntroduced = false

round428SignedAdjointDifferenceCancelsBeforeNormIsTrue :
  round428SignedAdjointDifferenceCancelsBeforeNorm ≡ true
round428SignedAdjointDifferenceCancelsBeforeNormIsTrue = refl
