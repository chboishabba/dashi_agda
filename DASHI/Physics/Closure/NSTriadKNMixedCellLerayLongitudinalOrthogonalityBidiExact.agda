module DASHI.Physics.Closure.NSTriadKNMixedCellLerayLongitudinalOrthogonalityBidiExact where

------------------------------------------------------------------------
-- MIXED CELL: OUTPUT-PROJECTED / LONGITUDINAL CROSS GRAM = 0
--
-- R286 defines
--   A_parallel = A - P_k A.
-- The literal Leray definition is
--   P_k A = A - c(A) k,
-- hence A_parallel = c(A) k by additive algebra.
--
-- R30 proves P_k A is transverse for k != 0.  Round84 proves every transverse
-- vector is Hermitian-orthogonal to a scalar multiple of k.  Therefore the
-- projected/longitudinal mixed Gram terms vanish exactly, before norms.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (0ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNPressureDirectionHermitianOrthogonalityRound84Exact as R84
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicitySplitRound286Exact as R286
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179

F : C3.RealField _
F = Rational.rationalRealField

subtractDifferenceRecovers :
  (a b : C3.Complex3 F) →
  C3.complex3Subtract a (C3.complex3Subtract a b) ≡ b
subtractDifferenceRecovers
    (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
  Field.complex3Ext
    (R.solve 2 (λ a b → a R.⊕ (R.⊝ (a R.⊕ (R.⊝ b))) R.⊜ b) refl ax bx)
    (R.solve 2 (λ a b → a R.⊕ (R.⊝ (a R.⊕ (R.⊝ b))) R.⊜ b) refl ay by)
    (R.solve 2 (λ a b → a R.⊕ (R.⊝ (a R.⊕ (R.⊝ b))) R.⊜ b) refl az bz)
  where module R = Ring.Solver F

lerayRankOneScalar :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (mode : Z3.FourierMode) →
  (value : C3.Complex3 F) →
  C3.Complex F
lerayRankOneScalar E I mode value =
  C3.complexMultiply
    (C3.realEmbed F (C3.inverseNormSquared I mode))
    (C3.bilinearDot3 (C3.modeVector E mode) value)

lerayLongitudinal :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (mode : Z3.FourierMode) →
  (value : C3.Complex3 F) →
  C3.Complex3 F
lerayLongitudinal E I mode value =
  C3.complex3Subtract value (C3.lerayProject3 E I mode value)

lerayLongitudinalIsRankOne :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (mode : Z3.FourierMode) →
  (value : C3.Complex3 F) →
  lerayLongitudinal E I mode value
  ≡ C3.complex3Scale
      (lerayRankOneScalar E I mode value)
      (C3.modeVector E mode)
lerayLongitudinalIsRankOne E I mode value =
  subtractDifferenceRecovers value
    (C3.complex3Scale
      (lerayRankOneScalar E I mode value)
      (C3.modeVector E mode))

mixedLongitudinalIsRankOne :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  R286.outputLongitudinalCell E I S velocity tau
  ≡ C3.complex3Scale
      (lerayRankOneScalar E I (Physical.k tau)
        (R286.mixedCell E I S velocity tau))
      (C3.modeVector E (Physical.k tau))
mixedLongitudinalIsRankOne E I S velocity tau =
  lerayLongitudinalIsRankOne E I (Physical.k tau)
    (R286.mixedCell E I S velocity tau)

projectedLongitudinalHermitianZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau sigma : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Physical.k sigma →
  Z3.NonZeroMode (Physical.k tau) →
  C3.hermitianPairing3
    (R286.outputProjectedCell E I S velocity tau)
    (R286.outputLongitudinalCell E I S velocity sigma)
  ≡ C3.complexZero F
projectedLongitudinalHermitianZero E I S velocity tau sigma sameOutput outputNonzero =
  let
    projectedT = R30.lerayOutputTransverseExact E I
      (Physical.k tau) outputNonzero
      (R286.mixedCell E I S velocity tau)
    sigmaRank = mixedLongitudinalIsRankOne E I S velocity sigma
  in
  trans
    (cong
      (C3.hermitianPairing3 (R286.outputProjectedCell E I S velocity tau))
      sigmaRank)
    (transportOutput sameOutput projectedT)
  where
  transportOutput :
    Physical.k tau ≡ Physical.k sigma →
    C3.bilinearDot3 (C3.modeVector E (Physical.k tau))
      (R286.outputProjectedCell E I S velocity tau) ≡ C3.complexZero F →
    C3.hermitianPairing3
      (R286.outputProjectedCell E I S velocity tau)
      (C3.complex3Scale
        (lerayRankOneScalar E I (Physical.k sigma)
          (R286.mixedCell E I S velocity sigma))
        (C3.modeVector E (Physical.k sigma)))
    ≡ C3.complexZero F
  transportOutput refl transverse =
    R84.hermitianTransverseLongitudinalRightZero
      E (Physical.k tau)
      (R286.outputProjectedCell E I S velocity tau)
      (lerayRankOneScalar E I (Physical.k tau)
        (R286.mixedCell E I S velocity sigma))
      transverse

projectedLongitudinalRealGramZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau sigma : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Physical.k sigma →
  Z3.NonZeroMode (Physical.k tau) →
  R179.realHermitianCross
    (R286.outputProjectedCell E I S velocity tau)
    (R286.outputLongitudinalCell E I S velocity sigma)
  ≡ 0ℚ
projectedLongitudinalRealGramZero E I S velocity tau sigma sameOutput outputNonzero =
  trans
    (R287.realHermitianCrossIsPairingReal
      (R286.outputProjectedCell E I S velocity tau)
      (R286.outputLongitudinalCell E I S velocity sigma))
    (cong C3.real
      (projectedLongitudinalHermitianZero
        E I S velocity tau sigma sameOutput outputNonzero))

mixedCellProjectedLongitudinalGramOrthogonalityClosed : Bool
mixedCellProjectedLongitudinalGramOrthogonalityClosed = true

mixedCellLongitudinalDiscarded : Bool
mixedCellLongitudinalDiscarded = false

clayPromotion : Bool
clayPromotion = false
