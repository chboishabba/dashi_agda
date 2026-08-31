module DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact where

------------------------------------------------------------------------
-- ROUND287 / EXACT GRAM CONSEQUENCES OF THE OUTPUT-HELICITY SPLIT
--
-- R286 keeps the literal R227 mixed cell and splits its output-transverse part
-- into the two helical eigenspaces.  This file transports the existing helical
-- orthogonality law into the exact real-Hermitian cross term used by the R179
-- Gram ledger.
--
-- Thus, for ANY two cells on the same output k,
--
--   Re < A_1^{k,+}, A_2^{k,-} > = 0
--   Re < A_1^{k,-}, A_2^{k,+} > = 0.
--
-- This is an exact covariance reduction before norms.  It does not give a sign
-- to the surviving ++ or -- cross-cell covariance.
--
-- We also prove two no-go symmetry facts on the same Gram scalar:
-- simultaneous conjugation and simultaneous negation preserve the real Gram
-- cross term.  Consequently a conjugate-output orbit or a double-sign orbit
-- duplicates the covariance; it does not cancel it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicitySplitRound286Exact as R286

F : C3.RealField _
F = Rational.rationalRealField

realHermitianCrossIsPairingReal :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross u v ≡ C3.real (C3.hermitianPairing3 u v)
realHermitianCrossIsPairingReal
    (C3.complex3
      (C3.complex ur ui) (C3.complex vr vi) (C3.complex wr wi))
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (ur ∷ ui ∷ vr ∷ vi ∷ wr ∷ wi ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

realHermitianCrossSymmetric :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross u v ≡ R179.realHermitianCross v u
realHermitianCrossSymmetric
    (C3.complex3
      (C3.complex ur ui) (C3.complex vr vi) (C3.complex wr wi))
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (ur ∷ ui ∷ vr ∷ vi ∷ wr ∷ wi ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

realHermitianCrossConjugateBoth :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross
    (C3.complex3Conjugate u) (C3.complex3Conjugate v)
  ≡ R179.realHermitianCross u v
realHermitianCrossConjugateBoth
    (C3.complex3
      (C3.complex ur ui) (C3.complex vr vi) (C3.complex wr wi))
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (ur ∷ ui ∷ vr ∷ vi ∷ wr ∷ wi ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

realHermitianCrossNegateBoth :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross
    (C3.complex3Negate u) (C3.complex3Negate v)
  ≡ R179.realHermitianCross u v
realHermitianCrossNegateBoth
    (C3.complex3
      (C3.complex ur ui) (C3.complex vr vi) (C3.complex wr wi))
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (ur ∷ ui ∷ vr ∷ vi ∷ wr ∷ wi ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

outputPlusMinusHermitianZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (u v : C3.Complex3 F) →
  C3.hermitianPairing3
    (Helical.helicalProjectorPlus E I S k u)
    (Helical.helicalProjectorMinus E I S k v)
  ≡ C3.complexZero F
outputPlusMinusHermitianZero E I S L k u v =
  Helical.helicalProjectorsOrthogonal L k u v

outputPlusMinusRealGramZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (u v : C3.Complex3 F) →
  R179.realHermitianCross
    (Helical.helicalProjectorPlus E I S k u)
    (Helical.helicalProjectorMinus E I S k v)
  ≡ 0ℚ
outputPlusMinusRealGramZero E I S L k u v =
  trans
    (realHermitianCrossIsPairingReal
      (Helical.helicalProjectorPlus E I S k u)
      (Helical.helicalProjectorMinus E I S k v))
    (cong C3.real (outputPlusMinusHermitianZero E I S L k u v))

outputMinusPlusRealGramZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (u v : C3.Complex3 F) →
  R179.realHermitianCross
    (Helical.helicalProjectorMinus E I S k u)
    (Helical.helicalProjectorPlus E I S k v)
  ≡ 0ℚ
outputMinusPlusRealGramZero E I S L k u v =
  trans
    (realHermitianCrossSymmetric
      (Helical.helicalProjectorMinus E I S k u)
      (Helical.helicalProjectorPlus E I S k v))
    (outputPlusMinusRealGramZero E I S L k v u)

physicalCellOutputPlusMinusGramZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau sigma : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Physical.k sigma →
  R179.realHermitianCross
    (R286.outputPlusCell E I S velocity tau)
    (R286.outputMinusCell E I S velocity sigma)
  ≡ 0ℚ
physicalCellOutputPlusMinusGramZero E I S L velocity tau sigma sameOutput =
  -- Transport sigma's output label to tau's output; the projector law then
  -- applies to the two literal mixed cells.
  substSigma sameOutput
    (outputPlusMinusRealGramZero E I S L (Physical.k tau)
      (R286.mixedCell E I S velocity tau)
      (R286.mixedCell E I S velocity sigma))
  where
  substSigma :
    Physical.k tau ≡ Physical.k sigma →
    R179.realHermitianCross
      (R286.outputPlusCell E I S velocity tau)
      (Helical.helicalProjectorMinus E I S (Physical.k tau)
        (R286.mixedCell E I S velocity sigma))
      ≡ 0ℚ →
    R179.realHermitianCross
      (R286.outputPlusCell E I S velocity tau)
      (R286.outputMinusCell E I S velocity sigma)
      ≡ 0ℚ
  substSigma refl proof = proof

round287OutputHelicityCrossGramExactlyZero : Bool
round287OutputHelicityCrossGramExactlyZero = true

round287ConjugatingBothCellsCancelsGram : Bool
round287ConjugatingBothCellsCancelsGram = false

round287NegatingBothCellsCancelsGram : Bool
round287NegatingBothCellsCancelsGram = false

round287SameHelicityCrossCellSignDetermined : Bool
round287SameHelicityCrossCellSignDetermined = false

round287PackageAClosed : Bool
round287PackageAClosed = false

round287ClayPromotion : Bool
round287ClayPromotion = false

round287OutputHelicityCrossGramExactlyZeroIsTrue :
  round287OutputHelicityCrossGramExactlyZero ≡ true
round287OutputHelicityCrossGramExactlyZeroIsTrue = refl

round287ConjugatingBothCellsCancelsGramIsFalse :
  round287ConjugatingBothCellsCancelsGram ≡ false
round287ConjugatingBothCellsCancelsGramIsFalse = refl
