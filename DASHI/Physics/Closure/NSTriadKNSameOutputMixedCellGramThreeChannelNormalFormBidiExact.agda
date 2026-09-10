module DASHI.Physics.Closure.NSTriadKNSameOutputMixedCellGramThreeChannelNormalFormBidiExact where

------------------------------------------------------------------------
-- SAME-OUTPUT MIXED-CELL GRAM -> ++ + -- + LONGITUDINAL/LONGITUDINAL
--
-- R286 decomposes every literal mixed-helicity cell at output k as
--
--   A = A+ + A- + Aparallel.
--
-- R287 kills the (+,-) and (-,+) output-helicity Gram channels.  The newer
-- Leray/longitudinal owner kills projected/longitudinal cross terms exactly for
-- one nonzero output.  Therefore, for two cells on that same nonzero output,
--
--   Re<A_alpha,A_gamma>
--     = Re<A+_alpha,A+_gamma>
--       + Re<A-_alpha,A-_gamma>
--       + Re<Aparallel_alpha,Aparallel_gamma>.
--
-- No sign, norm, or majorant is introduced.  This is the exact signed channel
-- normal form needed by the spectator-weighted amplitude Gram pair expansion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicitySplitRound286Exact as R286
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNMixedCellLerayLongitudinalOrthogonalityBidiExact as Long

F : C3.RealField _
F = Rational.rationalRealField

sameOutputLongitudinalProjectedZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau sigma : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Physical.k sigma →
  Z3.NonZeroMode (Physical.k tau) →
  R179.realHermitianCross
    (R286.outputLongitudinalCell E I S velocity tau)
    (R286.outputProjectedCell E I S velocity sigma)
  ≡ 0ℚ
sameOutputLongitudinalProjectedZero E I S velocity tau sigma sameOutput outputNonzero =
  trans
    (R287.realHermitianCrossSymmetric
      (R286.outputLongitudinalCell E I S velocity tau)
      (R286.outputProjectedCell E I S velocity sigma))
    (Long.projectedLongitudinalRealGramZero
      E I S velocity sigma tau (sym sameOutput)
      (transportNonzero sameOutput outputNonzero))
  where
  transportNonzero :
    Physical.k tau ≡ Physical.k sigma →
    Z3.NonZeroMode (Physical.k tau) →
    Z3.NonZeroMode (Physical.k sigma)
  transportNonzero refl nz = nz

sameOutputProjectedGramIsPlusPlusPlusMinusMinus :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau sigma : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Physical.k sigma →
  R179.realHermitianCross
    (R286.outputProjectedCell E I S velocity tau)
    (R286.outputProjectedCell E I S velocity sigma)
  ≡
  R179.realHermitianCross
    (R286.outputPlusCell E I S velocity tau)
    (R286.outputPlusCell E I S velocity sigma)
  +
  R179.realHermitianCross
    (R286.outputMinusCell E I S velocity tau)
    (R286.outputMinusCell E I S velocity sigma)
sameOutputProjectedGramIsPlusPlusPlusMinusMinus E I S L velocity tau sigma sameOutput =
  let
    tauSplit = R286.projectedCellIsOutputHelicitySum E I S L velocity tau
    sigmaSplit = R286.projectedCellIsOutputHelicitySum E I S L velocity sigma
    pp = R179.realHermitianCross
      (R286.outputPlusCell E I S velocity tau)
      (R286.outputPlusCell E I S velocity sigma)
    pm = R179.realHermitianCross
      (R286.outputPlusCell E I S velocity tau)
      (R286.outputMinusCell E I S velocity sigma)
    mp = R179.realHermitianCross
      (R286.outputMinusCell E I S velocity tau)
      (R286.outputPlusCell E I S velocity sigma)
    mm = R179.realHermitianCross
      (R286.outputMinusCell E I S velocity tau)
      (R286.outputMinusCell E I S velocity sigma)
    pmZero = R287.physicalCellOutputPlusMinusGramZero
      E I S L velocity tau sigma sameOutput
    mpZero : mp ≡ 0ℚ
    mpZero = trans
      (R287.realHermitianCrossSymmetric
        (R286.outputMinusCell E I S velocity tau)
        (R286.outputPlusCell E I S velocity sigma))
      (R287.physicalCellOutputPlusMinusGramZero
        E I S L velocity sigma tau (sym sameOutput))
  in
  trans
    (cong
      (λ left → R179.realHermitianCross left
        (R286.outputProjectedCell E I S velocity sigma))
      tauSplit)
    (trans
      (R291.realCrossAddLeft
        (R286.outputPlusCell E I S velocity tau)
        (R286.outputMinusCell E I S velocity tau)
        (R286.outputProjectedCell E I S velocity sigma))
      (trans
        (cong
          (λ right →
            R179.realHermitianCross
              (R286.outputPlusCell E I S velocity tau) right
            + R179.realHermitianCross
              (R286.outputMinusCell E I S velocity tau) right)
          sigmaSplit)
        (trans
          (cong₂ _+_
            (R291.realCrossAddRight
              (R286.outputPlusCell E I S velocity tau)
              (R286.outputPlusCell E I S velocity sigma)
              (R286.outputMinusCell E I S velocity sigma))
            (R291.realCrossAddRight
              (R286.outputMinusCell E I S velocity tau)
              (R286.outputPlusCell E I S velocity sigma)
              (R286.outputMinusCell E I S velocity sigma)))
          (trans
            (cong₂ _+_
              (cong (pp +_) pmZero)
              (cong (_+ mm) mpZero))
            (solve (pp ∷ mm ∷ [])))))))

sameOutputMixedGramThreeChannel :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau sigma : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Physical.k sigma →
  Z3.NonZeroMode (Physical.k tau) →
  R179.realHermitianCross
    (R286.mixedCell E I S velocity tau)
    (R286.mixedCell E I S velocity sigma)
  ≡
  R179.realHermitianCross
    (R286.outputPlusCell E I S velocity tau)
    (R286.outputPlusCell E I S velocity sigma)
  + R179.realHermitianCross
    (R286.outputMinusCell E I S velocity tau)
    (R286.outputMinusCell E I S velocity sigma)
  + R179.realHermitianCross
    (R286.outputLongitudinalCell E I S velocity tau)
    (R286.outputLongitudinalCell E I S velocity sigma)
sameOutputMixedGramThreeChannel E I S L velocity tau sigma sameOutput outputNonzero =
  let
    tauSplit = R286.mixedCellIsProjectedPlusLongitudinal E I S velocity tau
    sigmaSplit = R286.mixedCellIsProjectedPlusLongitudinal E I S velocity sigma
    projected = R179.realHermitianCross
      (R286.outputProjectedCell E I S velocity tau)
      (R286.outputProjectedCell E I S velocity sigma)
    longlong = R179.realHermitianCross
      (R286.outputLongitudinalCell E I S velocity tau)
      (R286.outputLongitudinalCell E I S velocity sigma)
    plZero = Long.projectedLongitudinalRealGramZero
      E I S velocity tau sigma sameOutput outputNonzero
    lpZero = sameOutputLongitudinalProjectedZero
      E I S velocity tau sigma sameOutput outputNonzero
    projectedSplit = sameOutputProjectedGramIsPlusPlusPlusMinusMinus
      E I S L velocity tau sigma sameOutput
  in
  trans
    (cong
      (λ left → R179.realHermitianCross left
        (R286.mixedCell E I S velocity sigma))
      tauSplit)
    (trans
      (R291.realCrossAddLeft
        (R286.outputProjectedCell E I S velocity tau)
        (R286.outputLongitudinalCell E I S velocity tau)
        (R286.mixedCell E I S velocity sigma))
      (trans
        (cong
          (λ right →
            R179.realHermitianCross
              (R286.outputProjectedCell E I S velocity tau) right
            + R179.realHermitianCross
              (R286.outputLongitudinalCell E I S velocity tau) right)
          sigmaSplit)
        (trans
          (cong₂ _+_
            (R291.realCrossAddRight
              (R286.outputProjectedCell E I S velocity tau)
              (R286.outputProjectedCell E I S velocity sigma)
              (R286.outputLongitudinalCell E I S velocity sigma))
            (R291.realCrossAddRight
              (R286.outputLongitudinalCell E I S velocity tau)
              (R286.outputProjectedCell E I S velocity sigma)
              (R286.outputLongitudinalCell E I S velocity sigma)))
          (trans
            (cong₂ _+_
              (cong (projected +_) plZero)
              (cong (_+ longlong) lpZero))
            (trans
              (solve (projected ∷ longlong ∷ []))
              (cong (_+ longlong) projectedSplit)))))))

sameOutputMixedGramThreeChannelClosed : Bool
sameOutputMixedGramThreeChannelClosed = true

sameOutputMixedGramCrossChannelsSurvive : Bool
sameOutputMixedGramCrossChannelsSurvive = false

sameOutputMixedGramSameHelicitySignsDetermined : Bool
sameOutputMixedGramSameHelicitySignsDetermined = false

clayPromotion : Bool
clayPromotion = false

sameOutputMixedGramThreeChannelClosedIsTrue :
  sameOutputMixedGramThreeChannelClosed ≡ true
sameOutputMixedGramThreeChannelClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
