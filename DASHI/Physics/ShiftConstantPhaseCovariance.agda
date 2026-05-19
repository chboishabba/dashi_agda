module DASHI.Physics.ShiftConstantPhaseCovariance where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; _+_; _*_; -[1+_])
open import Data.List.Base using (List; _∷_; [])
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
open import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.ShiftSpatialLaplacian as SSL

module RingZ = NR IntRS.ring
open RingZ using (Expr; Κ; _⊕_; _⊗_; _⊜_; solve)

------------------------------------------------------------------------
-- Exact finite global C4 phase covariance over the current static-gauge
-- wave lane.
--
-- This module closes only the bounded constant-phase vacuum slice:
--   * the covariant operator on the vacuum gauge commutes with a global
--     constant Phase4 action,
--   * the induced one-pass update therefore commutes with the same global
--     action.
--
-- No local gauge covariance, dynamic gauge-field evolution, or continuum
-- claim is implied.

constantPhaseField :
  SPTI4.Phase4 →
  SSL.ShiftWaveField →
  SSL.ShiftWaveField
constantPhaseField φ ψ =
  SFGS.transformMatter (SFGS.constantGaugeTransform φ) ψ

negDistrib+ :
  (x y : ℤ) →
  (-[1+ 0 ] * (x + y))
    ≡
  ((-[1+ 0 ] * x) + (-[1+ 0 ] * y))
negDistrib+ x y =
  RingZ.solve 2
    (λ x y →
      ( (Κ (-[1+ 0 ]) ⊗ (x ⊕ y))
      , ((Κ (-[1+ 0 ]) ⊗ x) ⊕ (Κ (-[1+ 0 ]) ⊗ y)) ))
    refl x y

negScaleComm :
  (k x : ℤ) →
  (-[1+ 0 ] * (k * x))
    ≡
  (k * (-[1+ 0 ] * x))
negScaleComm k x =
  RingZ.solve 2
    (λ k x →
      ( (Κ (-[1+ 0 ]) ⊗ (k ⊗ x))
      , (k ⊗ (Κ (-[1+ 0 ]) ⊗ x)) ))
    refl k x

doubleNegDistrib+ :
  (x y : ℤ) →
  (-[1+ 0 ] * (-[1+ 0 ] * (x + y)))
    ≡
  ((-[1+ 0 ] * (-[1+ 0 ] * x)) + (-[1+ 0 ] * (-[1+ 0 ] * y)))
doubleNegDistrib+ x y =
  RingZ.solve 2
    (λ x y →
      ( (Κ (-[1+ 0 ]) ⊗ (Κ (-[1+ 0 ]) ⊗ (x ⊕ y)))
      , ((Κ (-[1+ 0 ]) ⊗ (Κ (-[1+ 0 ]) ⊗ x))
         ⊕
         (Κ (-[1+ 0 ]) ⊗ (Κ (-[1+ 0 ]) ⊗ y))) ))
    refl x y

doubleNegScaleComm :
  (k x : ℤ) →
  (-[1+ 0 ] * (-[1+ 0 ] * (k * x)))
    ≡
  (k * (-[1+ 0 ] * (-[1+ 0 ] * x)))
doubleNegScaleComm k x =
  RingZ.solve 2
    (λ k x →
      ( (Κ (-[1+ 0 ]) ⊗ (Κ (-[1+ 0 ]) ⊗ (k ⊗ x)))
      , (k ⊗ (Κ (-[1+ 0 ]) ⊗ (Κ (-[1+ 0 ]) ⊗ x))) ))
    refl k x

phaseActWaveAdd :
  (φ : SPTI4.Phase4) →
  (ψ χ : SDWS.DiscreteWave) →
  SFGS.phaseAct φ (SDWS.waveAdd ψ χ)
    ≡
  SDWS.waveAdd (SFGS.phaseAct φ ψ) (SFGS.phaseAct φ χ)
phaseActWaveAdd SPTI4.φ0 ψ χ = refl
phaseActWaveAdd SPTI4.φ1 (SDWS.mkDiscreteWave reψ imψ) (SDWS.mkDiscreteWave reχ imχ)
  rewrite negDistrib+ imψ imχ
  = refl
phaseActWaveAdd SPTI4.φ2 (SDWS.mkDiscreteWave reψ imψ) (SDWS.mkDiscreteWave reχ imχ)
  rewrite negDistrib+ reψ reχ
        | negDistrib+ imψ imχ
  = refl
phaseActWaveAdd SPTI4.φ3 (SDWS.mkDiscreteWave reψ imψ) (SDWS.mkDiscreteWave reχ imχ)
  rewrite doubleNegDistrib+ imψ imχ
        | negDistrib+ reψ reχ
  = refl

phaseActScaleWave :
  (φ : SPTI4.Phase4) →
  (k : ℤ) →
  (ψ : SDWS.DiscreteWave) →
  SFGS.phaseAct φ (SDWS.scaleWave k ψ)
    ≡
  SDWS.scaleWave k (SFGS.phaseAct φ ψ)
phaseActScaleWave SPTI4.φ0 k ψ = refl
phaseActScaleWave SPTI4.φ1 k (SDWS.mkDiscreteWave reψ imψ)
  rewrite negScaleComm k imψ
  = refl
phaseActScaleWave SPTI4.φ2 k (SDWS.mkDiscreteWave reψ imψ)
  rewrite negScaleComm k reψ
        | negScaleComm k imψ
  = refl
phaseActScaleWave SPTI4.φ3 k (SDWS.mkDiscreteWave reψ imψ)
  rewrite doubleNegScaleComm k imψ
        | negScaleComm k reψ
  = refl

phaseActMulI :
  (φ : SPTI4.Phase4) →
  (ψ : SDWS.DiscreteWave) →
  SFGS.phaseAct φ (SDWS.mulI ψ)
    ≡
  SDWS.mulI (SFGS.phaseAct φ ψ)
phaseActMulI SPTI4.φ0 ψ = refl
phaseActMulI SPTI4.φ1 (SDWS.mkDiscreteWave reψ imψ) = refl
phaseActMulI SPTI4.φ2 (SDWS.mkDiscreteWave reψ imψ) = refl
phaseActMulI SPTI4.φ3 (SDWS.mkDiscreteWave reψ imψ) = refl

constantPhaseVacuumLaplacianCommutes :
  (φ : SPTI4.Phase4) →
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  SSL.shiftSpatialLaplacian (constantPhaseField φ ψ) s
    ≡
  SFGS.phaseAct φ (SSL.shiftSpatialLaplacian ψ s)
constantPhaseVacuumLaplacianCommutes φ ψ s
  rewrite phaseActWaveAdd φ (ψ (SSL.leftNeighbor s))
            (SDWS.waveAdd
              (ψ (SSL.rightNeighbor s))
              (SDWS.scaleWave (-[1+ 1 ]) (ψ s)))
        | phaseActWaveAdd φ (ψ (SSL.rightNeighbor s)) (SDWS.scaleWave (-[1+ 1 ]) (ψ s))
        | phaseActScaleWave φ (-[1+ 1 ]) (ψ s)
  = refl

ConstantPhaseVacuumOperatorCovariance : Set
ConstantPhaseVacuumOperatorCovariance =
  SFGC.ConstantPhaseVacuumCovarianceTarget

constantPhaseVacuumOperatorCovariance :
  ConstantPhaseVacuumOperatorCovariance
constantPhaseVacuumOperatorCovariance φ ψ s
  rewrite SFGC.constantGaugePreservesVacuum φ s
        | SFGC.vacuumGaugeCompatibility (constantPhaseField φ ψ) s
        | SFGC.vacuumGaugeCompatibility ψ s
        | constantPhaseVacuumLaplacianCommutes φ ψ s
  = refl

phaseActStepFrame :
  (φ : SPTI4.Phase4) →
  (ψ χ : SDWS.DiscreteWave) →
  SFGS.phaseAct φ (SDWS.waveAdd ψ (SDWS.mulI χ))
    ≡
  SDWS.waveAdd (SFGS.phaseAct φ ψ) (SDWS.mulI (SFGS.phaseAct φ χ))
phaseActStepFrame φ ψ χ
  rewrite phaseActWaveAdd φ ψ (SDWS.mulI χ)
        | phaseActMulI φ χ
  = refl

ConstantPhaseVacuumUpdateCovarianceTarget : Set
ConstantPhaseVacuumUpdateCovarianceTarget =
  (φ : SPTI4.Phase4) →
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  SFGC.gaugeGlobalUpdate
    SFGC.vacuumGaugeField
    (constantPhaseField φ ψ)
    s
    ≡
  SFGS.phaseAct φ
    (SFGC.gaugeGlobalUpdate SFGC.vacuumGaugeField ψ s)

record ShiftConstantPhaseCovariance : Setω where
  field
    matterField : Set
    staticGaugeField : Set
    gaugeCoupling : SFGC.ShiftFiniteGaugeCoupling
    symmetry : SFGS.ShiftFiniteGaugeSymmetry
    operatorCovarianceLaw : Set
    updateCovarianceTarget : Set
    nonClaimBoundary : List String

shiftConstantPhaseCovariance :
  ShiftConstantPhaseCovariance
shiftConstantPhaseCovariance =
  record
    { matterField = SSL.ShiftWaveField
    ; staticGaugeField = SFGC.GaugeField
    ; gaugeCoupling = SFGC.shiftFiniteGaugeCoupling
    ; symmetry = SFGS.shiftFiniteGaugeSymmetry
    ; operatorCovarianceLaw = ConstantPhaseVacuumOperatorCovariance
    ; updateCovarianceTarget = ConstantPhaseVacuumUpdateCovarianceTarget
    ; nonClaimBoundary =
        "Finite global C4 phase covariance package only"
        ∷ "covariance is only proved on the vacuum static-gauge slice of the current coarse carrier"
        ∷ "operator covariance is witnessed explicitly, while one-pass update covariance remains an exact target surface in this lane"
        ∷ "No local gauge covariance, dynamic gauge field, non-abelian symmetry, or continuum claim is implied"
        ∷ []
    }
