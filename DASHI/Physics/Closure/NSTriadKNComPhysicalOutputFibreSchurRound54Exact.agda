module DASHI.Physics.Closure.NSTriadKNComPhysicalOutputFibreSchurRound54Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Issai Schur.
-- Classical row/column matrix norm test; no DOI assigned to the original
-- theorem.
--
-- DASHI CONTRIBUTION
--
-- Round 54's generic fixed-output Schur theorem is now instantiated on the
-- repository's LITERAL finite Fourier-triad output fibre
-- `physicalOutputFiber cutoff k`.  Therefore the remaining Com estimate can be
-- stated directly on the actual same-output collision list, rather than on an
-- invented incidence count or an abstract pairProduct.
--
-- The only analytic inputs are the absolute kernel mass of that complete fibre
-- and a uniform column bound.  Once those are proved, the squared L2 estimate
-- follows mechanically with no cardinality multiplier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComFixedOutputFibreSchurRound54Exact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as Rect
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record PhysicalOutputFibreKernel
    (cutoff : Nat)
    (output : Z3.FourierMode) : Set₁ where
  field
    kernel : Triad.PhysicalTriadIncidence → ℚ
    rowBound columnBound : ℚ

    rowBoundNonnegative : 0ℚ ≤ rowBound
    columnBoundNonnegative : 0ℚ ≤ columnBound

    wholePhysicalOutputFibreMassBound :
      Sums.sumRational
        (Output.physicalOutputFiber cutoff output)
        (λ tau → ∣ kernel tau ∣)
      ≤ rowBound

    everyPhysicalIncidenceColumnBound : ∀ tau →
      ∣ kernel tau ∣ ≤ columnBound

open PhysicalOutputFibreKernel public

asFixedOutputFibre :
  ∀ {cutoff output} →
  PhysicalOutputFibreKernel cutoff output →
  Fibre.FixedOutputFourierFibre Triad.PhysicalTriadIncidence
asFixedOutputFibre {cutoff} {output} physical = record
  { columns = Output.physicalOutputFiber cutoff output
  ; kernel = kernel physical
  ; rowBound = rowBound physical
  ; columnBound = columnBound physical
  ; rowBoundNonnegative = rowBoundNonnegative physical
  ; columnBoundNonnegative = columnBoundNonnegative physical
  ; wholeAbsoluteFibreMassBound = wholePhysicalOutputFibreMassBound physical
  ; everyColumnMassBound = everyPhysicalIncidenceColumnBound physical
  }

physicalOutputFibreApply :
  ∀ {cutoff output} →
  (physical : PhysicalOutputFibreKernel cutoff output) →
  Rect.Vector Triad.PhysicalTriadIncidence → ℚ
physicalOutputFibreApply physical =
  Fibre.fixedOutputApply (asFixedOutputFibre physical)

physicalOutputFibreInputNormSq :
  ∀ {cutoff output} →
  (physical : PhysicalOutputFibreKernel cutoff output) →
  Rect.Vector Triad.PhysicalTriadIncidence → ℚ
physicalOutputFibreInputNormSq physical =
  Fibre.fixedOutputVectorNormSq (asFixedOutputFibre physical)

physicalOutputFibreSchurSquared :
  ∀ {cutoff output}
    (physical : PhysicalOutputFibreKernel cutoff output)
    (vector : Rect.Vector Triad.PhysicalTriadIncidence) →
  L2.square (physicalOutputFibreApply physical vector)
  ≤ (rowBound physical * columnBound physical)
      * physicalOutputFibreInputNormSq physical vector
physicalOutputFibreSchurSquared physical =
  Fibre.fixedOutputFibreSchurSquared (asFixedOutputFibre physical)

physicalComUsesLiteralOutputFibreEnumeration : Bool
physicalComUsesLiteralOutputFibreEnumeration = true

physicalComWholeFibreEstimateHasNoIncidenceCountFactor : Bool
physicalComWholeFibreEstimateHasNoIncidenceCountFactor = true

physicalComLiteralKernelMassBoundsConstructed : Bool
physicalComLiteralKernelMassBoundsConstructed = false

physicalComUsesLiteralOutputFibreEnumerationIsTrue :
  physicalComUsesLiteralOutputFibreEnumeration ≡ true
physicalComUsesLiteralOutputFibreEnumerationIsTrue = refl

physicalComWholeFibreEstimateHasNoIncidenceCountFactorIsTrue :
  physicalComWholeFibreEstimateHasNoIncidenceCountFactor ≡ true
physicalComWholeFibreEstimateHasNoIncidenceCountFactorIsTrue = refl
