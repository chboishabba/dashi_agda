module DASHI.Physics.Closure.NSTriadKNComLiteralOutputFibreKernelRound57Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- ROUND 57 CONTRIBUTION
--
-- Construct the literal Fourier transport kernel on the ACTUAL finite output
-- fibre before taking absolute values.  For a resonant triad p+q=k, the
-- transport entry from input q to output k has advector p.  This is not an
-- invented kernel: it is exactly the coefficient already used by the physical
-- transport skew-adjoint theorem.
--
-- The still-open same-object seam is now narrower: project this literal kernel
-- to the physical odd P/Q cross channel and prove the common-hat / absolute
-- fibre-mass bounds.  Skewness itself is inherited here and must not be
-- reproved downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix

triadTransportEntry :
  (tau : Triad.PhysicalTriadIncidence) →
  Matrix.PhysicalTransportMatrixEntry (Triad.q tau) (Triad.k tau)
triadTransportEntry tau =
  Matrix.physical-transport-matrix-entry
    (Triad.p tau)
    (Triad.resonance tau)

literalTriadTransportCoefficient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Triad.PhysicalTriadIncidence → C3.Complex F
literalTriadTransportCoefficient E velocity tau =
  Matrix.transportEntryCoefficient E velocity (triadTransportEntry tau)

literalOutputFibreTransportCoefficient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  Triad.PhysicalTriadIncidence → C3.Complex F
literalOutputFibreTransportCoefficient E velocity cutoff output =
  literalTriadTransportCoefficient E velocity

fibreMemberHasLiteralOutput :
  ∀ {cutoff output tau} →
  tau Cube.∈ Output.physicalOutputFiber cutoff output →
  Triad.k tau ≡ output
fibreMemberHasLiteralOutput = Output.physicalOutputFiberSound

literalTriadKernelInheritsPhysicalSkew :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (tau : Triad.PhysicalTriadIncidence) →
  C3.complexConjugate
    (Matrix.transportEntryCoefficient E velocity
      (Matrix.reverseEntry (triadTransportEntry tau)))
  ≡ C3.complexNegate (literalTriadTransportCoefficient E velocity tau)
literalTriadKernelInheritsPhysicalSkew velocity reality divergenceFree tau =
  Matrix.physicalTransportMatrixEntrySkewAdjoint
    velocity reality divergenceFree (triadTransportEntry tau)

record LiteralPhysicalOutputFibreKernel
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat)
    (output : Z3.FourierMode) : Set where
  field
    reality : Audit.RealityCondition velocity
    divergenceFree : Audit.DivergenceFreeCondition E velocity

  coefficient : Triad.PhysicalTriadIncidence → C3.Complex F
  coefficient = literalTriadTransportCoefficient E velocity

open LiteralPhysicalOutputFibreKernel public

literalOutputFibreKernelUsesActualTriadEnumeration : Bool
literalOutputFibreKernelUsesActualTriadEnumeration = true

literalOutputFibreKernelSkewInherited : Bool
literalOutputFibreKernelSkewInherited = true

physicalOddPQProjectionOfLiteralFibreKernelConstructed : Bool
physicalOddPQProjectionOfLiteralFibreKernelConstructed = false

literalOutputFibreKernelUsesActualTriadEnumerationIsTrue :
  literalOutputFibreKernelUsesActualTriadEnumeration ≡ true
literalOutputFibreKernelUsesActualTriadEnumerationIsTrue = refl

literalOutputFibreKernelSkewInheritedIsTrue :
  literalOutputFibreKernelSkewInherited ≡ true
literalOutputFibreKernelSkewInheritedIsTrue = refl
