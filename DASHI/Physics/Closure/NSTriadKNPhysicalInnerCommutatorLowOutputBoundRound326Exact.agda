module DASHI.Physics.Closure.NSTriadKNPhysicalInnerCommutatorLowOutputBoundRound326Exact where

------------------------------------------------------------------------
-- ROUND326 / PHYSICAL INNER COMMUTATOR HAS A RADICAL-FREE LOW-OUTPUT BOUND
--
-- R325 proves exactly
--
--   pureCommutatorVector
--     = (-i) P_k(rawDirectionalSlotKernel).
--
-- R178 proves on the literal rational lattice, for a resonant transverse pair,
--
--   ||rawDirectionalSlotKernel||^2
--     <= 9 |k|^2 ||u_p||^2 ||u_q||^2,
--
-- with no high-leg frequency and no fibre-cardinality factor.
--
-- Leray is norm-contracting and multiplication by -i preserves squared norm.
-- Therefore the actual R120 paired Galerkin forcing obeys the same low-output
-- bound.  This closes the physical same-object content behind R312's exponent
-- relocation without using R232's open helical-basis/angular-symbol weld and
-- without introducing irrational radii/unit directions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNPressureHessianOrderedTermRationalBoundRound85Exact as R85
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNPureCommutatorRawDualDefectWeldRound325Exact as R325

F : C3.RealField _
F = Rational.rationalRealField

rawKernelAgreement :
  (waveP waveQ uP uQ : C3.Complex3 F) →
  R172.rawDirectionalSlotKernel waveP waveQ uP uQ
  ≡ R145.slotKernel waveP waveQ uP uQ
rawKernelAgreement waveP waveQ uP uQ = refl

minusIModulusSquaredIsOne :
  L2.complexModulusSquared (R106.minusI F) ≡ 1ℚ
minusIModulusSquaredIsOne = solve []

minusIScalePreservesNormSquared :
  (v : C3.Complex3 F) →
  L2.complex3NormSquared (C3.complex3Scale (R106.minusI F) v)
  ≡ L2.complex3NormSquared v
minusIScalePreservesNormSquared v =
  trans
    (R85.complex3ScaleNormSquared (R106.minusI F) v)
    (trans
      (cong (_* L2.complex3NormSquared v) minusIModulusSquaredIsOne)
      (ℚP.*-identityˡ (L2.complex3NormSquared v)))

physicalInnerPureCommutatorLowOutputBound :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (tau : Physical.PhysicalTriadIncidence)
  (H : R120.PhysicalHelicalOutputPair system tau) →
  Helical.Transverse E (Physical.p tau)
    (Audit.velocity system (Physical.p tau)) →
  Helical.Transverse E (Physical.q tau)
    (Audit.velocity system (Physical.q tau)) →
  L2.complex3NormSquared (R120.pureCommutatorVector system tau H)
  ≤ R178.nine * C3.normSquared I (Physical.k tau)
      * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
      * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))
physicalInnerPureCommutatorLowOutputBound E I O system tau H pTrans qTrans =
  let
    p = Physical.p tau
    q = Physical.q tau
    k = Physical.k tau
    uP = Audit.velocity system p
    uQ = Audit.velocity system q
    raw = R172.rawDirectionalSlotKernel
      (C3.modeVector E p) (C3.modeVector E q) uP uQ
    projectedRaw = C3.lerayProject3 E I k raw
    target = R178.nine * C3.normSquared I k
      * L2.complex3NormSquared uP
      * L2.complex3NormSquared uQ

    rawBound :
      L2.complex3NormSquared raw ≤ target
    rawBound =
      subst
        (λ selected → L2.complex3NormSquared selected ≤ target)
        (sym (rawKernelAgreement
          (C3.modeVector E p) (C3.modeVector E q) uP uQ))
        (R178.rawLowOutputKernelMassBound
          E I uP uQ (Physical.resonance tau) pTrans qTrans)

    projectedBound :
      L2.complex3NormSquared projectedRaw ≤ target
    projectedBound =
      ℚP.≤-trans
        (Leray.rationalLerayNormSquaredContraction
          E I O k raw (R120.outputNonzero H))
        rawBound

    scaledBound :
      L2.complex3NormSquared
        (C3.complex3Scale (R106.minusI F) projectedRaw)
      ≤ target
    scaledBound =
      subst
        (λ lower → lower ≤ target)
        (sym (minusIScalePreservesNormSquared projectedRaw))
        projectedBound

    sameObject = R325.pureCommutatorIsMinusIProjectedRawKernel system tau H
  in
  subst
    (λ selected → L2.complex3NormSquared selected ≤ target)
    (sym sameObject)
    scaledBound

round326PhysicalR120R178SameObjectBoundClosed : Bool
round326PhysicalR120R178SameObjectBoundClosed = true

round326HighLegFrequencyAppearsInBound : Bool
round326HighLegFrequencyAppearsInBound = false

round326FibreCardinalityFactorAppears : Bool
round326FibreCardinalityFactorAppears = false

round326UsesR232PhysicalAngularBasisWeld : Bool
round326UsesR232PhysicalAngularBasisWeld = false

round326R312PhysicalDerivativeRelocationWeldClosed : Bool
round326R312PhysicalDerivativeRelocationWeldClosed = true

round326NestedInnerFibreAggregationClosed : Bool
round326NestedInnerFibreAggregationClosed = false

round326HeatSchurClosed : Bool
round326HeatSchurClosed = false

round326PackageAClosed : Bool
round326PackageAClosed = false

round326ClayPromotion : Bool
round326ClayPromotion = false

round326PackageAClosedIsFalse : round326PackageAClosed ≡ false
round326PackageAClosedIsFalse = refl

round326ClayPromotionIsFalse : round326ClayPromotion ≡ false
round326ClayPromotionIsFalse = refl
