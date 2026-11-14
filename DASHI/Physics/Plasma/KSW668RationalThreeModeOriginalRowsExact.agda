module DASHI.Physics.Plasma.KSW668RationalThreeModeOriginalRowsExact where

------------------------------------------------------------------------
-- A1 original sparse Fourier SOURCE ROWS on the actual rational C3 carrier.
-- The original all-mode global Reality/DivFree producer still must be proved
-- (see Source.stateFromGloballyCheckedSource). The source row equalities are
-- not arbitrary scalars or invented Galerkin dynamics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation as Ordered
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Plasma.KSW668RationalThreeModeSourceExact as Source
import DASHI.Physics.Plasma.KSW668MHDSelectedStateTransferExact as Transfer

F : C3.RealField _
F = Rational.rationalRealField

sourcePlusAtQ :
  Source.sourceZPlus Source.q ≡ Source.plusQ
sourcePlusAtQ = refl

sourcePlusAtK :
  Source.sourceZPlus Source.k ≡ Source.plusK
sourcePlusAtK = refl

sourceMinusAtPPositive :
  Source.sourceZMinus Source.plusSigned Source.p ≡ Source.minusP
sourceMinusAtPPositive = refl

sourceMinusAtPNegative :
  Source.sourceZMinus Source.minusSigned Source.p
    ≡ Source.minusNegativeP
sourceMinusAtPNegative = refl

sourceDoubledMagneticKPositive :
  Source.sourceDoubledSquaredMagnetic Source.plusSigned Source.k
  ≡ (+ 2) / 1
sourceDoubledMagneticKPositive = solve []

sourceDoubledMagneticKNegative :
  Source.sourceDoubledSquaredMagnetic Source.minusSigned Source.k
  ≡ (+ 2) / 1
sourceDoubledMagneticKNegative = solve []

sourceDoubledMagneticQPositive :
  Source.sourceDoubledSquaredMagnetic Source.plusSigned Source.q
  ≡ 1ℚ
sourceDoubledMagneticQPositive = solve []

sourceDoubledMagneticQNegative :
  Source.sourceDoubledSquaredMagnetic Source.minusSigned Source.q
  ≡ 1ℚ
sourceDoubledMagneticQNegative = solve []

-- Same exact *original* Galerkin/projected nonlinear functional applied
-- to the provided original source coefficients, not an unrelated transfer.
selectedSourceNormalForm :
  (E : C3.IntegerEmbedding F) →
  Source.SelectedTransferSign → C3.Complex F
selectedSourceNormalForm E sign =
  C3.complexRealPart
    (C3.complexMultiply
      (Ordered.minusI F)
      (C3.complexMultiply
        (C3.bilinearDot3
          (Source.sourceZMinus sign Source.p)
          (C3.modeVector E Source.q))
        (C3.hermitianPairing3
          (Source.sourceZPlus Source.k)
          (Source.sourceZPlus Source.q))))

selectedPositiveSignFromOriginalSource :
  (E : C3.IntegerEmbedding F) →
  selectedSourceNormalForm E Source.plusSigned
    ≡ C3.realEmbed F (C3.embedInteger E (+ 1))
selectedPositiveSignFromOriginalSource E
  rewrite C3.embedZero E =
  Algebra.complexExt
    (solve (C3.embedInteger E (+ 1) ∷ []))
    refl

selectedNegativeSignFromOriginalSource :
  (E : C3.IntegerEmbedding F) →
  selectedSourceNormalForm E Source.minusSigned
    ≡ C3.realEmbed F (- (C3.embedInteger E (+ 1)))
selectedNegativeSignFromOriginalSource E
  rewrite C3.embedZero E =
  Algebra.complexExt
    (solve (C3.embedInteger E (+ 1) ∷ []))
    refl

-- The remaining all-mode reality/transversality hypotheses are recorded
-- without pretending to be the missing proof or a physical MMS measurement.
originalTransferFromGloballyValidatedSource :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (sign : Source.SelectedTransferSign)
  (rp : Audit.RealityCondition Source.sourceZPlus)
  (rm : Audit.RealityCondition (Source.sourceZMinus sign))
  (dp : Audit.DivergenceFreeCondition E Source.sourceZPlus)
  (dm : Audit.DivergenceFreeCondition E (Source.sourceZMinus sign)) →
    Transfer.selectedPlusTransfer I
    (Source.stateFromGloballyCheckedSource E sign rp rm dp dm)
    Source.k Source.p Source.q
  ≡ selectedSourceNormalForm E sign
originalTransferFromGloballyValidatedSource E I sign rp rm dp dm =
  Transfer.originalMHDSelectedNormalFormFromState I
    (Source.stateFromGloballyCheckedSource E sign rp rm dp dm)
    Source.k Source.p Source.q
