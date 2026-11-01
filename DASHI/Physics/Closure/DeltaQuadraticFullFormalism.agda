module DASHI.Physics.Closure.DeltaQuadraticFullFormalism where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Integer using (ℤ; +_; _-_)
open import Data.Vec using (Vec)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.SignatureUniqueness31 as SU
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QCB
open import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DTQ
open import DASHI.Physics.Closure.DeltaQuadraticEnergyExact as DQE
open import DASHI.Physics.Closure.PrimeWeightedQuadraticForm as PWQ

------------------------------------------------------------------------
-- Consolidated Delta -> quadratic -> signature -> Clifford formalism.
--
-- This module deliberately composes the repository's existing owners:
--
-- * arithmetic valuation amplitudes: WeightedValuationEnergy;
-- * exact unweighted energy: DeltaQuadraticEnergyExact;
-- * admissibility and normalization: ContractionForcesQuadraticStrong;
-- * theorem-level contraction package: ContractionForcesQuadraticTheorem;
-- * Lorentz signature: ContractionQuadraticToSignatureBridgeTheorem;
-- * Clifford factorization: QuadraticToCliffordBridgeTheorem;
-- * weighted geometry: PrimeWeightedQuadraticForm.
--
-- It does not identify raw cancellation pressure with quadratic energy.

DeltaState : Set
DeltaState = AIE.Int

DeltaAmplitude : DeltaState → Vec ℤ 15
DeltaAmplitude = WVE.valuationVecℤ

QDelta : DeltaState → ℤ
QDelta = DQE.QDelta

QDeltaFormCorrect :
  ∀ n → QDelta n ≡ QP.Q̂core (DeltaAmplitude n)
QDeltaFormCorrect = DQE.QDeltaFormCorrect

------------------------------------------------------------------------
-- Exact prime-weighted diagonal geometry.
--
-- This realizes the finite tracked-prime analogue of
--   Σ_p w_p v_p(n)^2
-- directly as a diagonal quadratic form over Vec ℤ 15.  The canonical exact
-- weights are the tracked primes themselves.  A logarithmic/real-valued
-- weighting remains a scalar-extension refinement, not an integer theorem.

QDeltaWeighted : DeltaState → ℤ
QDeltaWeighted n =
  QF.QuadraticForm.Q PWQ.primeWeightedQuadraticForm (DeltaAmplitude n)

QDeltaWeightedFormCorrect :
  ∀ n →
  QDeltaWeighted n
  ≡
  PWQ.weightedQ PWQ.primeWeightsℤ (WVE.valuationVecℤ n)
QDeltaWeightedFormCorrect n = refl

QDeltaWeightedMatchesArithmeticEnergy :
  ∀ n →
  QDeltaWeighted n ≡ + (WVE.weightedQuadraticEnergy n)
QDeltaWeightedMatchesArithmeticEnergy n = refl

------------------------------------------------------------------------
-- Delta-local residual and threshold/Lyapunov surface.
--
-- The local law is a map on the already-established quadratic carrier.
-- Its residual is the energy removed in one step:
--
--   R_Delta(x) = Q(x) - Q(Delta x).
--
-- A threshold system supplies the domain on which this residual is accepted as
-- a strict/ordered drop.  The Lyapunov theorem is then constructive transport
-- of that witness; no independent dynamics or order is invented here.

record DeltaLocalLaw (m : Nat) : Setω where
  field
    step :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {m})

open DeltaLocalLaw public

quadraticResidual :
  ∀ {m} →
  QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ →
  DeltaLocalLaw m →
  PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
  ℤ
quadraticResidual q delta x =
  QF.QuadraticForm.Q q x -
  QF.QuadraticForm.Q q (DeltaLocalLaw.step delta x)

quadraticResidualCorrect :
  ∀ {m}
    (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ)
    (delta : DeltaLocalLaw m)
    x →
  quadraticResidual q delta x
  ≡
  QF.QuadraticForm.Q q x -
  QF.QuadraticForm.Q q (DeltaLocalLaw.step delta x)
quadraticResidualCorrect q delta x = refl

record DeltaThresholdSystem
  (m : Nat)
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ)
  (delta : DeltaLocalLaw m) : Setω where
  field
    Below : ℤ → ℤ → Set
    thresholdAdmissible :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m}) → Set
    stepDropsEnergyBelowThreshold :
      ∀ {x} →
      thresholdAdmissible x →
      Below
        (QF.QuadraticForm.Q q (DeltaLocalLaw.step delta x))
        (QF.QuadraticForm.Q q x)

open DeltaThresholdSystem public

QDeltaLyapunov :
  ∀ {m q delta}
    (system : DeltaThresholdSystem m q delta)
    {x} →
  DeltaThresholdSystem.thresholdAdmissible system x →
  DeltaThresholdSystem.Below system
    (QF.QuadraticForm.Q q (DeltaLocalLaw.step delta x))
    (QF.QuadraticForm.Q q x)
QDeltaLyapunov system admissible =
  DeltaThresholdSystem.stepDropsEnergyBelowThreshold system admissible

------------------------------------------------------------------------
-- Reduction to the existing admissibility/normalization seam.

QDeltaToAdmissibleQuadratic :
  (dynamicsMap :
    PD.Additive.Carrier (QES.AdditiveVecℤ {15}) →
    PD.Additive.Carrier (QES.AdditiveVecℤ {15})) →
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {15}) QES.ScalarFieldℤ) →
  CFQS.AdmissibleFor 15 dynamicsMap q →
  ∀ n →
  QDelta n ≡ QF.QuadraticForm.Q q (DeltaAmplitude n)
QDeltaToAdmissibleQuadratic =
  DQE.exactDeltaAgreesWithAdmissibleQuadratic

QDeltaDeterminesAdmissibleQuadraticsOnImage :
  (dynamicsMap :
    PD.Additive.Carrier (QES.AdditiveVecℤ {15}) →
    PD.Additive.Carrier (QES.AdditiveVecℤ {15})) →
  (q1 q2 : QF.QuadraticForm (QES.AdditiveVecℤ {15}) QES.ScalarFieldℤ) →
  CFQS.AdmissibleFor 15 dynamicsMap q1 →
  CFQS.AdmissibleFor 15 dynamicsMap q2 →
  ∀ n →
  QF.QuadraticForm.Q q1 (DeltaAmplitude n)
  ≡
  QF.QuadraticForm.Q q2 (DeltaAmplitude n)
QDeltaDeterminesAdmissibleQuadraticsOnImage =
  DQE.exactDeltaDeterminesAdmissibleQuadraticsOnImage

------------------------------------------------------------------------
-- Signature and Clifford inheritance.
--
-- The Delta bridge does not recompute either object.  Once the candidate is
-- admitted through the existing theorem surface, normalization, signature
-- (3,1), and Clifford factorization are inherited from their canonical owners.

DeltaBridgeNormalizesToQ̂core :
  (bridge : DTQ.DeltaToQuadraticBridgeTheorem) →
  ∀ x →
  QF.QuadraticForm.Q
    (DTQ.DeltaToQuadraticBridgeTheorem.deltaQuadratic bridge)
    x
  ≡ QP.Q̂core x
DeltaBridgeNormalizesToQ̂core =
  DTQ.DeltaToQuadraticBridgeTheorem.normalizedDeltaQuadratic

DeltaBridgeSignature31Theorem :
  DTQ.DeltaToQuadraticBridgeTheorem →
  SU.Signature31Theorem
DeltaBridgeSignature31Theorem =
  DTQ.DeltaToQuadraticBridgeTheorem.inheritedSignature31Theorem

DeltaBridgeForcesLorentz31 :
  (bridge : DTQ.DeltaToQuadraticBridgeTheorem) →
  DTQ.DeltaToQuadraticBridgeTheorem.inheritedSignature31Value bridge
  ≡ CTI.sig31
DeltaBridgeForcesLorentz31 =
  DTQ.DeltaToQuadraticBridgeTheorem.inheritedSignatureForced31

record DeltaQuadraticClosurePackage : Setω where
  field
    deltaBridge : DTQ.DeltaToQuadraticBridgeTheorem
    cliffordBridge : QCB.QuadraticToCliffordBridgeTheorem
    cliffordPresentation :
      QCB.CliffordPresentation
        (CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
          (DTQ.DeltaToQuadraticBridgeTheorem.contractionQuadraticToSignatureBridge
            deltaBridge))

  normalizedQuadratic :
    ∀ x →
    QF.QuadraticForm.Q
      (DTQ.DeltaToQuadraticBridgeTheorem.deltaQuadratic deltaBridge)
      x
    ≡ QP.Q̂core x
  normalizedQuadratic = DeltaBridgeNormalizesToQ̂core deltaBridge

  signature31 : SU.Signature31Theorem
  signature31 = DeltaBridgeSignature31Theorem deltaBridge

  lorentz31Forced :
    DTQ.DeltaToQuadraticBridgeTheorem.inheritedSignature31Value deltaBridge
    ≡ CTI.sig31
  lorentz31Forced = DeltaBridgeForcesLorentz31 deltaBridge

  existingSignatureCliffordPackage :
    DTQ.DeltaQuadraticSignatureCliffordPackage
  existingSignatureCliffordPackage =
    DTQ.deltaBridgeToSignatureCliffordPackage
      deltaBridge cliffordBridge cliffordPresentation

------------------------------------------------------------------------
-- Weighted-to-canonical boundary.
--
-- The prime-weighted quadratic is now a real `QuadraticForm`, but it is not
-- silently normalized to the unweighted Q-hat-core.  Such a promotion must
-- explicitly supply the geometric comparison it claims.

record WeightedToCanonicalSeam : Setω where
  field
    dynamicsMap :
      PD.Additive.Carrier (QES.AdditiveVecℤ {15}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {15})
    weightedAdmissible :
      CFQS.AdmissibleFor 15 dynamicsMap PWQ.primeWeightedQuadraticForm

  weightedNormalizesToQ̂core :
    ∀ x →
    QF.QuadraticForm.Q PWQ.primeWeightedQuadraticForm x
    ≡ QP.Q̂core x
  weightedNormalizesToQ̂core =
    CFQS.admissibleForNormalization weightedAdmissible

  weightedDeltaEnergyNormalizesOnImage :
    ∀ n → QDeltaWeighted n ≡ QP.Q̂core (DeltaAmplitude n)
  weightedDeltaEnergyNormalizesOnImage n =
    weightedNormalizesToQ̂core (DeltaAmplitude n)
