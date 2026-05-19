module DASHI.Physics.ShiftWaveEnergyHierarchy where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveEnergy as SDWE
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftWaveRefinementHierarchy as SWRH
open import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- Theorem-thin finite energy hierarchy for the current concrete 3 -> 5
-- refinement stack.
--
-- This module stays fully finite and enumerative:
--   * field energy is the sum of pointwise integer-pair square norms,
--   * the lifted 5-point field duplicates the coarse endpoint energies on the
--     reflected shadows,
--   * the lifted 5-point Laplacian has zero endpoint-shadow energy and exact
--     agreement with the coarse Laplacian energy on embedded points.
--
-- No norm convergence, PDE limit, or positivity theorem is claimed.

coarseFieldEnergy :
  SWRH.ShiftWaveField3 →
  ℤ
coarseFieldEnergy wf =
  SDWE.waveNormSq (wf SPTI.shiftStartPoint)
    +ℤ
  SDWE.waveNormSq (wf SPTI.shiftNextPoint)
    +ℤ
  SDWE.waveNormSq (wf SPTI.shiftHeldExitPoint)

fineFieldEnergy :
  SWRH.ShiftWaveField5 →
  ℤ
fineFieldEnergy wf =
  SDWE.waveNormSq (wf SWRH.s0)
    +ℤ
  SDWE.waveNormSq (wf SWRH.s1)
    +ℤ
  SDWE.waveNormSq (wf SWRH.s2)
    +ℤ
  SDWE.waveNormSq (wf SWRH.s3)
    +ℤ
  SDWE.waveNormSq (wf SWRH.s4)

coarseLaplacianEnergy :
  SWRH.ShiftWaveField3 →
  ℤ
coarseLaplacianEnergy wf =
  SDWE.waveNormSq (SSL.shiftSpatialLaplacian wf SPTI.shiftStartPoint)
    +ℤ
  SDWE.waveNormSq (SSL.shiftSpatialLaplacian wf SPTI.shiftNextPoint)
    +ℤ
  SDWE.waveNormSq (SSL.shiftSpatialLaplacian wf SPTI.shiftHeldExitPoint)

fineLaplacianEnergy :
  SWRH.ShiftWaveField5 →
  ℤ
fineLaplacianEnergy wf =
  SDWE.waveNormSq (SWRH.shiftSpatialLaplacian5 wf SWRH.s0)
    +ℤ
  SDWE.waveNormSq (SWRH.shiftSpatialLaplacian5 wf SWRH.s1)
    +ℤ
  SDWE.waveNormSq (SWRH.shiftSpatialLaplacian5 wf SWRH.s2)
    +ℤ
  SDWE.waveNormSq (SWRH.shiftSpatialLaplacian5 wf SWRH.s3)
    +ℤ
  SDWE.waveNormSq (SWRH.shiftSpatialLaplacian5 wf SWRH.s4)

embeddedFineLaplacianEnergy :
  SWRH.ShiftWaveField5 →
  ℤ
embeddedFineLaplacianEnergy wf =
  SDWE.waveNormSq (SWRH.shiftSpatialLaplacian5 wf SWRH.s1)
    +ℤ
  SDWE.waveNormSq (SWRH.shiftSpatialLaplacian5 wf SWRH.s2)
    +ℤ
  SDWE.waveNormSq (SWRH.shiftSpatialLaplacian5 wf SWRH.s3)

LiftFieldEnergyShape3to5 : Set
LiftFieldEnergyShape3to5 =
  (wf : SWRH.ShiftWaveField3) →
  fineFieldEnergy (SWRH.liftField3to5 wf)
    ≡
  SDWE.waveNormSq (wf SPTI.shiftStartPoint)
    +ℤ
  SDWE.waveNormSq (wf SPTI.shiftStartPoint)
    +ℤ
  SDWE.waveNormSq (wf SPTI.shiftNextPoint)
    +ℤ
  SDWE.waveNormSq (wf SPTI.shiftHeldExitPoint)
    +ℤ
  SDWE.waveNormSq (wf SPTI.shiftHeldExitPoint)

liftFieldEnergyShape3to5 : LiftFieldEnergyShape3to5
liftFieldEnergyShape3to5 wf = refl

LiftLaplacianEnergyControl3to5 : Set
LiftLaplacianEnergyControl3to5 =
  (wf : SWRH.ShiftWaveField3) →
  embeddedFineLaplacianEnergy (SWRH.liftField3to5 wf)
    ≡
  coarseLaplacianEnergy wf

liftLaplacianEnergyControl3to5 :
  LiftLaplacianEnergyControl3to5
liftLaplacianEnergyControl3to5 wf
  rewrite SWRH.laplacianConsistency3to5 wf SPTI.shiftStartPoint
        | SWRH.laplacianConsistency3to5 wf SPTI.shiftNextPoint
        | SWRH.laplacianConsistency3to5 wf SPTI.shiftHeldExitPoint
  = refl

record ShiftWaveEnergyHierarchy : Setω where
  field
    coarseField : Set
    fineField : Set
    coarseEnergy :
      coarseField → ℤ
    fineEnergy :
      fineField → ℤ
    coarseLaplacianEnergySurface :
      coarseField → ℤ
    fineLaplacianEnergySurface :
      fineField → ℤ
    liftEnergyShape :
      Set
    liftLaplacianControl :
      Set
    nonClaimBoundary : List String

shiftWaveEnergyHierarchy :
  ShiftWaveEnergyHierarchy
shiftWaveEnergyHierarchy =
  record
    { coarseField = SWRH.ShiftWaveField3
    ; fineField = SWRH.ShiftWaveField5
    ; coarseEnergy = coarseFieldEnergy
    ; fineEnergy = fineFieldEnergy
    ; coarseLaplacianEnergySurface = coarseLaplacianEnergy
    ; fineLaplacianEnergySurface = fineLaplacianEnergy
    ; liftEnergyShape = LiftFieldEnergyShape3to5
    ; liftLaplacianControl = LiftLaplacianEnergyControl3to5
    ; nonClaimBoundary =
        "Finite 3-point to 5-point energy hierarchy only"
        ∷ "Field energy is the exact sum of pointwise integer-pair square norms"
        ∷ "The 5-point lift duplicates endpoint energy on reflected shadow points"
        ∷ "Laplacian-energy control is exact only on the embedded coarse window s1,s2,s3 under the current projection lift"
        ∷ "No full five-point Laplacian-energy equality or separate shadow-cancellation theorem is claimed at this layer"
        ∷ "No norm convergence, coercivity, spectral theorem, positivity theorem, or PDE limit claim is implied"
        ∷ []
    }
