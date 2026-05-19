module DASHI.Physics.ShiftDiscreteHelmholtzSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; -[1+_])
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import DASHI.Physics.ShiftWaveRefinementHierarchy as SWRH

------------------------------------------------------------------------
-- Discrete Helmholtz / modewise Schrödinger surface over the current finite
-- spatial operators.
--
-- This packages the field-level reading
--   H = -Δ
-- and the finite eigenmode law
--   ψ ↦ ψ + i λ ψ
-- whenever a field satisfies the corresponding discrete Helmholtz equation.
-- It stays explicitly below unitarity, spectral completeness, or PDE claims.

cong :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

waveNeg : SDWS.DiscreteWave → SDWS.DiscreteWave
waveNeg ψ =
  SDWS.scaleWave (-[1+ 0 ]) ψ

coarseHamiltonian :
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
coarseHamiltonian ψ s =
  waveNeg (SSL.shiftSpatialLaplacian ψ s)

fineHamiltonian :
  SWRH.ShiftWaveField5 →
  SWRH.ShiftPressurePoint5 →
  SDWS.DiscreteWave
fineHamiltonian ψ s =
  waveNeg (SWRH.shiftSpatialLaplacian5 ψ s)

coarseHelmholtzResidual :
  ℤ →
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
coarseHelmholtzResidual eig ψ s =
  SDWS.waveAdd
    (coarseHamiltonian ψ s)
    (waveNeg (SDWS.scaleWave eig (ψ s)))

fineHelmholtzResidual :
  ℤ →
  SWRH.ShiftWaveField5 →
  SWRH.ShiftPressurePoint5 →
  SDWS.DiscreteWave
fineHelmholtzResidual eig ψ s =
  SDWS.waveAdd
    (fineHamiltonian ψ s)
    (waveNeg (SDWS.scaleWave eig (ψ s)))

IsCoarseEigenmode : ℤ → SSL.ShiftWaveField → Set
IsCoarseEigenmode eig ψ =
  (s : SPTI.ShiftPressurePoint) →
  coarseHamiltonian ψ s ≡ SDWS.scaleWave eig (ψ s)

IsFineEigenmode : ℤ → SWRH.ShiftWaveField5 → Set
IsFineEigenmode eig ψ =
  (s : SWRH.ShiftPressurePoint5) →
  fineHamiltonian ψ s ≡ SDWS.scaleWave eig (ψ s)

fieldSchrodingerStep3 :
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
fieldSchrodingerStep3 ψ s =
  SDWS.waveAdd
    (ψ s)
    (SDWS.mulI (coarseHamiltonian ψ s))

fieldSchrodingerStep5 :
  SWRH.ShiftWaveField5 →
  SWRH.ShiftPressurePoint5 →
  SDWS.DiscreteWave
fieldSchrodingerStep5 ψ s =
  SDWS.waveAdd
    (ψ s)
    (SDWS.mulI (fineHamiltonian ψ s))

CoarseEigenmodeStepLaw : ℤ → SSL.ShiftWaveField → Set
CoarseEigenmodeStepLaw eig ψ =
  IsCoarseEigenmode eig ψ →
  (s : SPTI.ShiftPressurePoint) →
  fieldSchrodingerStep3 ψ s
    ≡
  SDWS.waveAdd
    (ψ s)
    (SDWS.mulI (SDWS.scaleWave eig (ψ s)))

FineEigenmodeStepLaw : ℤ → SWRH.ShiftWaveField5 → Set
FineEigenmodeStepLaw eig ψ =
  IsFineEigenmode eig ψ →
  (s : SWRH.ShiftPressurePoint5) →
  fieldSchrodingerStep5 ψ s
    ≡
  SDWS.waveAdd
    (ψ s)
    (SDWS.mulI (SDWS.scaleWave eig (ψ s)))

coarseEigenmodeStepWitness :
  (eig : ℤ) →
  (ψ : SSL.ShiftWaveField) →
  CoarseEigenmodeStepLaw eig ψ
coarseEigenmodeStepWitness eig ψ eigen s =
  cong
    (λ h → SDWS.waveAdd (ψ s) (SDWS.mulI h))
    (eigen s)

fineEigenmodeStepWitness :
  (eig : ℤ) →
  (ψ : SWRH.ShiftWaveField5) →
  FineEigenmodeStepLaw eig ψ
fineEigenmodeStepWitness eig ψ eigen s =
  cong
    (λ h → SDWS.waveAdd (ψ s) (SDWS.mulI h))
    (eigen s)

record ShiftDiscreteHelmholtzSurface : Setω where
  field
    coarseField : Set
    fineField : Set
    coarseResidual :
      ℤ → coarseField → SPTI.ShiftPressurePoint → SDWS.DiscreteWave
    fineResidual :
      ℤ → fineField → SWRH.ShiftPressurePoint5 → SDWS.DiscreteWave
    coarseEigenmode :
      ℤ → coarseField → Set
    fineEigenmode :
      ℤ → fineField → Set
    nonClaimBoundary : List String

shiftDiscreteHelmholtzSurface :
  ShiftDiscreteHelmholtzSurface
shiftDiscreteHelmholtzSurface =
  record
    { coarseField = SSL.ShiftWaveField
    ; fineField = SWRH.ShiftWaveField5
    ; coarseResidual = coarseHelmholtzResidual
    ; fineResidual = fineHelmholtzResidual
    ; coarseEigenmode = IsCoarseEigenmode
    ; fineEigenmode = IsFineEigenmode
    ; nonClaimBoundary =
        "Finite discrete Helmholtz surface only"
        ∷ "Hamiltonian is the negative finite spatial Laplacian"
        ∷ "Eigenmode law is modewise packaging for the finite Euler-style Schrodinger step"
        ∷ "No spectral completeness, orthogonality basis, self-adjointness, or PDE claim is implied"
        ∷ []
    }
