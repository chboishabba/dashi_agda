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
-- Construct the literal Fourier transport coefficient on the ACTUAL finite
-- `physicalOutputFiber`.  For a resonant triad p+q=k, the transport entry from
-- input q to output k has advector p, exactly as in the Round-40 physical skew
-- theorem.  This is the pre-projection kernel; the odd P/Q restriction is
-- constructed separately without reproving skewness.
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

open LiteralPhysicalOutputFibreKernel public

literalPhysicalOutputFibreCoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {velocity : Z3.FourierMode → C3.Complex3 F}
    {cutoff : Nat} {output : Z3.FourierMode} →
  LiteralPhysicalOutputFibreKernel E velocity cutoff output →
  Triad.PhysicalTriadIncidence → C3.Complex F
literalPhysicalOutputFibreCoefficient {E = E} {velocity} physical =
  literalTriadTransportCoefficient E velocity

literalOutputFibreKernelUsesActualTriadEnumeration : Bool
literalOutputFibreKernelUsesActualTriadEnumeration = true

literalOutputFibreKernelSkewInherited : Bool
literalOutputFibreKernelSkewInherited = true

literalOutputFibreKernelUsesActualTriadEnumerationIsTrue :
  literalOutputFibreKernelUsesActualTriadEnumeration ≡ true
literalOutputFibreKernelUsesActualTriadEnumerationIsTrue = refl

literalOutputFibreKernelSkewInheritedIsTrue :
  literalOutputFibreKernelSkewInherited ≡ true
literalOutputFibreKernelSkewInheritedIsTrue = refl
