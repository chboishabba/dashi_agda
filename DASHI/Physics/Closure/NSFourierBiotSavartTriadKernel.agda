module DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.Closure.NSPairIncidenceKernel

------------------------------------------------------------------------
-- Exact Fourier-vorticity convention for the finite NS transfer kernel.
--
-- For vorticity omega at a nonzero Fourier mode p, the Biot--Savart velocity
-- carrier is
--
--   u_p = |p|^-2 (p x omega_p).
--
-- For p + q = k, the vorticity interaction convention used here is
--
--   T(p,q; omega_p, omega_q)
--     = (omega_p . q) u_q - (u_p . q) omega_q.
--
-- The linearized transfer about a background bar-omega is the sum
--
--   T(p,q; bar-omega_p, eta_q)
--   + T(q,p; eta_q, bar-omega_p).
--
-- The rectangular Schur kernel is the declared nonnegative majorant of this
-- vector, inserted only at the matching target/source entry (k,q).  Phase and
-- sign cancellation are not used by this majorant lane.
------------------------------------------------------------------------

record FourierVectorLaws
    {m v s : Level}
    (Mode : Set m)
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    scalarZero : Scalar
    scalarAdd scalarMultiply : Scalar → Scalar → Scalar
    scalarOrder : Scalar → Scalar → Set s

    vectorZero : Vector
    vectorAdd vectorSubtract : Vector → Vector → Vector
    vectorScale : Scalar → Vector → Vector
    vectorDot : Vector → Vector → Scalar
    vectorCross : Vector → Vector → Vector

    waveVector : Mode → Vector
    inverseNormSquared : Mode → Scalar

    modeDelta : Mode → Mode → Scalar
    vectorMajorant : Vector → Scalar

open FourierVectorLaws public

biotSavartVelocity :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  FourierVectorLaws Mode Vector Scalar →
  Mode → Vector → Vector
biotSavartVelocity L mode omega =
  vectorScale L
    (inverseNormSquared L mode)
    (vectorCross L (waveVector L mode) omega)

fourierVorticityTriad :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  FourierVectorLaws Mode Vector Scalar →
  Mode → Mode → Vector → Vector → Vector
fourierVorticityTriad L p q omegaP omegaQ =
  vectorSubtract L
    (vectorScale L
      (vectorDot L omegaP (waveVector L q))
      (biotSavartVelocity L q omegaQ))
    (vectorScale L
      (vectorDot L (biotSavartVelocity L p omegaP) (waveVector L q))
      omegaQ)

record ResonantFourierTriad
    {m : Level}
    (Mode : Set m)
    (addMode : Mode → Mode → Mode)
    (NonZeroMode : Mode → Set m) : Set (lsuc m) where
  field
    pMode qMode targetMode : Mode
    resonance : addMode pMode qMode ≡ targetMode
    pNonZero : NonZeroMode pMode
    qNonZero : NonZeroMode qMode

open ResonantFourierTriad public

record FourierBiotSavartTransferData
    {m v s : Level}
    (Mode : Set m)
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    laws : FourierVectorLaws Mode Vector Scalar

    addMode : Mode → Mode → Mode
    NonZeroMode : Mode → Set m
    triads : List (ResonantFourierTriad Mode addMode NonZeroMode)

    targetModes : List Mode
    sourceModes : List Mode

    backgroundVorticity : Mode → Vector
    perturbationPolarization : Mode → Vector

    backgroundDivergenceFree :
      ∀ mode →
      vectorDot laws
        (waveVector laws mode)
        (backgroundVorticity mode)
      ≡ scalarZero laws

    perturbationDivergenceFree :
      ∀ mode →
      vectorDot laws
        (waveVector laws mode)
        (perturbationPolarization mode)
      ≡ scalarZero laws

    targetWeight : Mode → Scalar
    sourceWeight : Mode → Scalar

open FourierBiotSavartTransferData public

linearizedTriadVector :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  (F : FourierBiotSavartTransferData Mode Vector Scalar) →
  ResonantFourierTriad Mode (addMode F) (NonZeroMode F) →
  Vector
linearizedTriadVector F triad =
  vectorAdd (laws F)
    (fourierVorticityTriad (laws F)
      (pMode triad)
      (qMode triad)
      (backgroundVorticity F (pMode triad))
      (perturbationPolarization F (qMode triad)))
    (fourierVorticityTriad (laws F)
      (qMode triad)
      (pMode triad)
      (perturbationPolarization F (qMode triad))
      (backgroundVorticity F (pMode triad)))

fourierPairContribution :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  (F : FourierBiotSavartTransferData Mode Vector Scalar) →
  ResonantFourierTriad Mode (addMode F) (NonZeroMode F) →
  Mode → Mode → Scalar
fourierPairContribution F triad target source =
  scalarMultiply (laws F)
    (modeDelta (laws F) (targetMode triad) target)
    (scalarMultiply (laws F)
      (modeDelta (laws F) (qMode triad) source)
      (vectorMajorant (laws F) (linearizedTriadVector F triad)))

fourierPairIncidenceData :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  FourierBiotSavartTransferData Mode Vector Scalar →
  PairIncidenceData
    (ResonantFourierTriad Mode
      (addMode _)
      (NonZeroMode _))
    Mode Mode Scalar
fourierPairIncidenceData F = record
  { pairs = triads F
  ; rows = targetModes F
  ; columns = sourceModes F
  ; zero = scalarZero (laws F)
  ; add = scalarAdd (laws F)
  ; multiply = scalarMultiply (laws F)
  ; _≤_ = scalarOrder (laws F)
  ; pairContribution = fourierPairContribution F
  ; rowWeight = targetWeight F
  ; colWeight = sourceWeight F
  }

fourierBiotSavartKernel :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  (F : FourierBiotSavartTransferData Mode Vector Scalar) →
  Mode → Mode → Scalar
fourierBiotSavartKernel F =
  pairKernelEntry (fourierPairIncidenceData F)

fourierKernelIsPairIncidence :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  (F : FourierBiotSavartTransferData Mode Vector Scalar) →
  ConcreteBiotSavartKernelMatch
    (fourierPairIncidenceData F)
    (fourierBiotSavartKernel F)
fourierKernelIsPairIncidence F = record
  { pointwiseKernelMatch = λ target source → refl }
