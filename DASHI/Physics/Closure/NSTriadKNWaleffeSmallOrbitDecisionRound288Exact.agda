module DASHI.Physics.Closure.NSTriadKNWaleffeSmallOrbitDecisionRound288Exact where

------------------------------------------------------------------------
-- ROUND288 / SMALLEST SAME-OUTPUT COVARIANCE EXPERIMENT
--
-- Decision question:
--   after recovering the Waleffe/output-helicity structure of the literal
--   R227 cell, does the smallest two-cell same-output Gram orbit acquire an
--   algebraically forced sign before any estimate?
--
-- R286 gives, for the output-transverse part,
--
--   P_k A = A^{k,+} + A^{k,-}.
--
-- R287 gives exact cross-helicity orthogonality.  Hence for two distinct cells
-- A,B on the SAME output fibre,
--
--   Re <P_k A, P_k B>
--     = Re <A^{k,+},B^{k,+}> + Re <A^{k,-},B^{k,-}>.
--
-- This is a genuine exact reduction: all +-/-+ output-helicity covariance is
-- gone before norms.  But the two surviving same-helicity scalars have no sign
-- from projector orthogonality alone.
--
-- Moreover, R287 proves simultaneous conjugation and simultaneous negation
-- preserve the real Gram scalar.  Thus the obvious reality/double-sign orbits
-- do not supply cancellation.  The p/q swap also does not act internally on
-- the chosen R227 (+,-) family: R224 sends it through the (-,+) family that was
-- removed only after whole-fibre reindexing.
--
-- BIDI DECISION:
--   this does NOT refute every possible pointwise theta<1 estimate, but it
--   removes the cheapest symmetry mechanism for one.  The highest-alpha next
--   attack is therefore the signed TEMPORAL/FLUX route to R222, while the R283
--   spatial route remains available if a deeper same-helicity phase identity
--   is later found.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicitySplitRound286Exact as R286
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287

F : C3.RealField _
F = Rational.rationalRealField

realCrossAddBoth :
  (a b c d : C3.Complex3 F) →
  R179.realHermitianCross
    (C3.complex3Add a b) (C3.complex3Add c d)
  ≡
  (R179.realHermitianCross a c + R179.realHermitianCross a d)
  + (R179.realHermitianCross b c + R179.realHermitianCross b d)
realCrossAddBoth
    (C3.complex3
      (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci))
    (C3.complex3
      (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi))
    (C3.complex3
      (C3.complex gr gi) (C3.complex hr hi) (C3.complex ir ii))
    (C3.complex3
      (C3.complex jr ji) (C3.complex kr ki) (C3.complex lr li)) =
  solve
    ( ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci
    ∷ dr ∷ di ∷ er ∷ ei ∷ fr ∷ fi
    ∷ gr ∷ gi ∷ hr ∷ hi ∷ ir ∷ ii
    ∷ jr ∷ ji ∷ kr ∷ ki ∷ lr ∷ li ∷ [])

sameOutputMinusPlusZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau sigma : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Physical.k sigma →
  R179.realHermitianCross
    (R286.outputMinusCell E I S velocity tau)
    (R286.outputPlusCell E I S velocity sigma)
  ≡ 0ℚ
sameOutputMinusPlusZero E I S L velocity tau sigma sameOutput =
  trans
    (R287.realHermitianCrossSymmetric
      (R286.outputMinusCell E I S velocity tau)
      (R286.outputPlusCell E I S velocity sigma))
    (R287.physicalCellOutputPlusMinusGramZero
      E I S L velocity sigma tau (sym sameOutput))

projectedTwoCellGramSplitsByOutputHelicity :
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
projectedTwoCellGramSplitsByOutputHelicity
    E I S L velocity tau sigma sameOutput =
  let
    plusTau = R286.outputPlusCell E I S velocity tau
    minusTau = R286.outputMinusCell E I S velocity tau
    plusSigma = R286.outputPlusCell E I S velocity sigma
    minusSigma = R286.outputMinusCell E I S velocity sigma

    expand :
      R179.realHermitianCross
        (C3.complex3Add plusTau minusTau)
        (C3.complex3Add plusSigma minusSigma)
      ≡
      (R179.realHermitianCross plusTau plusSigma
        + R179.realHermitianCross plusTau minusSigma)
      +
      (R179.realHermitianCross minusTau plusSigma
        + R179.realHermitianCross minusTau minusSigma)
    expand = realCrossAddBoth plusTau minusTau plusSigma minusSigma

    pmZero : R179.realHermitianCross plusTau minusSigma ≡ 0ℚ
    pmZero = R287.physicalCellOutputPlusMinusGramZero
      E I S L velocity tau sigma sameOutput

    mpZero : R179.realHermitianCross minusTau plusSigma ≡ 0ℚ
    mpZero = sameOutputMinusPlusZero
      E I S L velocity tau sigma sameOutput

    collapse :
      (R179.realHermitianCross plusTau plusSigma
        + R179.realHermitianCross plusTau minusSigma)
      +
      (R179.realHermitianCross minusTau plusSigma
        + R179.realHermitianCross minusTau minusSigma)
      ≡
      R179.realHermitianCross plusTau plusSigma
      + R179.realHermitianCross minusTau minusSigma
    collapse rewrite pmZero | mpZero =
      solve
        (R179.realHermitianCross plusTau plusSigma
        ∷ R179.realHermitianCross minusTau minusSigma ∷ [])
  in
  trans
    (cong₂ R179.realHermitianCross
      (R286.projectedCellIsOutputHelicitySum E I S L velocity tau)
      (R286.projectedCellIsOutputHelicitySum E I S L velocity sigma))
    (trans expand collapse)

round288CrossOutputHelicityCovarianceEliminatedExactly : Bool
round288CrossOutputHelicityCovarianceEliminatedExactly = true

round288ConjugationOrbitForcesNegativeOrNullGram : Bool
round288ConjugationOrbitForcesNegativeOrNullGram = false

round288DoubleSignOrbitForcesNegativeOrNullGram : Bool
round288DoubleSignOrbitForcesNegativeOrNullGram = false

round288SwapIsInternalInChosenPlusMinusFamily : Bool
round288SwapIsInternalInChosenPlusMinusFamily = false

round288SameHelicitySpatialSignStillPossibleButNotDerived : Bool
round288SameHelicitySpatialSignStillPossibleButNotDerived = true

round288TemporalFluxRouteHighestAlpha : Bool
round288TemporalFluxRouteHighestAlpha = true

round288PointwiseRelativeAbsorptionClosed : Bool
round288PointwiseRelativeAbsorptionClosed = false

round288PackageAClosed : Bool
round288PackageAClosed = false

round288ClayPromotion : Bool
round288ClayPromotion = false

round288CrossOutputHelicityCovarianceEliminatedExactlyIsTrue :
  round288CrossOutputHelicityCovarianceEliminatedExactly ≡ true
round288CrossOutputHelicityCovarianceEliminatedExactlyIsTrue = refl

round288TemporalFluxRouteHighestAlphaIsTrue :
  round288TemporalFluxRouteHighestAlpha ≡ true
round288TemporalFluxRouteHighestAlphaIsTrue = refl
