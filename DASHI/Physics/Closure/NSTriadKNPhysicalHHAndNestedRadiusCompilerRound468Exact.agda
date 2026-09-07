module DASHI.Physics.Closure.NSTriadKNPhysicalHHAndNestedRadiusCompilerRound468Exact where

------------------------------------------------------------------------
-- ROUND468 / ONE R467 GEOMETRY OWNER -> R177 + R431
--
-- R467 proves the literal normalized-direction complement.  This module does
-- not add another estimate.  It compiles that one theorem into both historical
-- consumers:
--
--   * R177 unconditional pointwise HH low-output gain;
--   * R431 literal nested outer-slot radius calibration.
--
-- The only extra representation datum is the orientation of the selected
-- helical radius scalar: modeNorm >= 0.  Its square and reciprocal laws are
-- already supplied by the R464 MHD/NS calibration package.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralOrderedPairWaleffeFactorRound93Exact as R93
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNHHDualDefectUnconditionalPointwiseRound177Exact as R177
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNLiteralNestedOuterRadiusDefectRound431Exact as R431
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact as R464
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedAntiParallelComplementRound467Exact as R467

F : C3.RealField _
F = Rational.rationalRealField

record PhysicalRadiusOrientation
    (S : Helical.HelicalModeScalars F) : Set where
  constructor physical-radius-orientation
  field
    modeNormNonnegative :
      (mode : Z3.FourierMode) → 0ℚ ≤ Helical.modeNorm S mode

open PhysicalRadiusOrientation public

physicalComplementForIncidence :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F) →
  R464.PhysicalSquareAndMHDCalibration E I S →
  PhysicalRadiusOrientation S →
  (tau : Physical.PhysicalTriadIncidence) →
  R467.PhysicalNormalizedComplementData E I S
    (Physical.p tau) (Physical.q tau) (Physical.k tau)
physicalComplementForIncidence E I S C O tau = record
  { R467.resonance = R93.resonanceRecord tau
  ; R467.squareP = R464.squareCalibration C (Physical.p tau)
  ; R467.squareQ = R464.squareCalibration C (Physical.q tau)
  ; R467.squareK = R464.squareCalibration C (Physical.k tau)
  ; R467.reciprocalP = R464.reciprocalCalibration C (Physical.p tau)
  ; R467.reciprocalQ = R464.reciprocalCalibration C (Physical.q tau)
  ; R467.reciprocalK = R464.reciprocalCalibration C (Physical.k tau)
  ; R467.radiusPNN = modeNormNonnegative O (Physical.p tau)
  ; R467.radiusQNN = modeNormNonnegative O (Physical.q tau)
  ; R467.radiusKNN = modeNormNonnegative O (Physical.k tau)
  }

toR177SymmetricDualDefectData :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  (a b : C3.Complex3 F) →
  R145.TransverseHighPair
    (R167.normalizedDirection E S p)
    (R167.normalizedDirection E S q) a b →
  R177.SymmetricDualDefectData
toR177SymmetricDualDefectData {E} {I} {S} {p} {q} {k} D a b transverse = record
  { R177.rp = Helical.modeNorm S p
  ; R177.rq = Helical.modeNorm S q
  ; R177.rk = Helical.modeNorm S k
  ; R177.P = R167.normalizedDirection E S p
  ; R177.Q = R167.normalizedDirection E S q
  ; R177.a = a
  ; R177.b = b
  ; R177.rpNN = R467.radiusPNN D
  ; R177.rqNN = R467.radiusQNN D
  ; R177.unitP = R455.normalizedDirectionUnit E I S p (R467.r455P D)
  ; R177.unitQ = R455.normalizedDirectionUnit E I S q (R467.r455Q D)
  ; R177.transverse = transverse
  ; R177.complement = R467.physicalNormalizedComplementIdentity D
  }
  where
  import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455

physicalHHPointwiseOutputBound :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  (a b : C3.Complex3 F) →
  (transverse : R145.TransverseHighPair
    (R167.normalizedDirection E S p)
    (R167.normalizedDirection E S q) a b) →
  R177.R176.norm
    (R177.rawKernel (toR177SymmetricDualDefectData D a b transverse))
  ≤ R177.R175.twentyFour
      * R177.R176.square (Helical.modeNorm S k)
      * (R177.R176.norm a * R177.R176.norm b)
physicalHHPointwiseOutputBound D a b transverse =
  R177.unconditionalPointwiseHHOutputBound
    (toR177SymmetricDualDefectData D a b transverse)

toR431LiteralOuterRadiusCalibration :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  (calibration : R464.PhysicalSquareAndMHDCalibration E I S) →
  (orientation : PhysicalRadiusOrientation S) →
  R431.LiteralOuterRadiusCalibration E I O system S L H W C
toR431LiteralOuterRadiusCalibration E I O system S L H W C calibration orientation =
  let
    tau = R329.outer C
    D = physicalComplementForIncidence E I S calibration orientation tau
  in
  record
    { R431.radiusP = Helical.modeNorm S (Physical.p tau)
    ; R431.radiusQ = Helical.modeNorm S (Physical.q tau)
    ; R431.radiusK = Helical.modeNorm S (Physical.k tau)
    ; R431.radiusPMeaning = refl
    ; R431.radiusQMeaning = refl
    ; R431.outputRadiusSquareMeaning =
        R464.modeNormSquareMeaning (R464.squareCalibration calibration (Physical.k tau))
    ; R431.radiusProductNN = R467.radiusProductNonnegative D
    ; R431.outputSquareNN = R467.outputRadiusSquareNonnegative D
    ; R431.scaledNormalizedDefectBound =
        R467.scaledNormalizedDefectBelowOutputSquare D
    }

literalOuterSlotDivisionFreeLowOutputBoundFromPhysicalCalibration :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  (calibration : R464.PhysicalSquareAndMHDCalibration E I S) →
  (orientation : PhysicalRadiusOrientation S) →
  let cal = toR431LiteralOuterRadiusCalibration
        E I O system S L H W C calibration orientation
  in
  (R431.radiusP cal * R431.radiusQ cal)
    * L2.complex3NormSquared
        (R329.literalNestedOuterSlot E I O system S L H W C)
  ≤ R174.twelve
      * (C3.normSquared I (Physical.k (R329.outer C))
        * L2.complex3NormSquared
            (R329.innerPairedForcing E I O system S L H W C)
        * L2.complex3NormSquared
            (Audit.velocity system (Physical.q (R329.outer C))))
literalOuterSlotDivisionFreeLowOutputBoundFromPhysicalCalibration
    E I O system S L H W C calibration orientation =
  R431.literalOuterSlotDivisionFreeLowOutputBound
    E I O system S L H W C
    (toR431LiteralOuterRadiusCalibration
      E I O system S L H W C calibration orientation)
  where
  import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174

round468R177PhysicalPointwiseHHCompilerClosed : Bool
round468R177PhysicalPointwiseHHCompilerClosed = true

round468R431PhysicalRadiusCalibrationCompilerClosed : Bool
round468R431PhysicalRadiusCalibrationCompilerClosed = true

round468ExternalHelicalBasisAngularFormulaRequired : Bool
round468ExternalHelicalBasisAngularFormulaRequired = false

round468ContainsPostulate : Bool
round468ContainsPostulate = false

round468PackageAClosed : Bool
round468PackageAClosed = false

round468ClayPromotion : Bool
round468ClayPromotion = false

round468ExternalHelicalBasisAngularFormulaRequiredIsFalse :
  round468ExternalHelicalBasisAngularFormulaRequired ≡ false
round468ExternalHelicalBasisAngularFormulaRequiredIsFalse = refl

round468ContainsPostulateIsFalse : round468ContainsPostulate ≡ false
round468ContainsPostulateIsFalse = refl
