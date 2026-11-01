module DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Promote Round 40's literal resonant coefficient identity to the actual
-- matrix-entry statement.  A matrix entry from input q to output k owns the
-- unique advector displacement m together with m+q=k.  The reverse entry is
-- the exact lattice displacement -m from k back to q; this module proves the
-- reverse resonance rather than assuming it.
--
-- For every real divergence-free velocity state,
--
--   conjugate T(q,k) = - T(k,q).
--
-- This is the pointwise matrix identity T*=-T.  No function extensionality is
-- needed: finite operator/Gram assemblies can consume the equality entry by
-- entry.  The remaining Com seam is therefore only the identification of the
-- literal odd P/Q block entries with the existing Round-35 Gram cells.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact as Coeff

record PhysicalTransportMatrixEntry
    (input output : Z3.FourierMode) : Set where
  constructor physical-transport-matrix-entry
  field
    advector : Z3.FourierMode
    resonance : Z3.addMode advector input ≡ output

open PhysicalTransportMatrixEntry public

reverseResonance :
  ∀ {input output}
    (entry : PhysicalTransportMatrixEntry input output) →
  Z3.addMode (Z3.negateMode (advector entry)) output ≡ input
reverseResonance {input} {output} entry =
  trans
    (Symmetry.addModeCommutative
      (Z3.negateMode (advector entry)) output)
    (trans
      (cong
        (λ selected →
          Z3.addMode selected (Z3.negateMode (advector entry)))
        (sym (resonance entry)))
      (Orbit.addNegateLeft (advector entry) input))

reverseEntry :
  ∀ {input output} →
  PhysicalTransportMatrixEntry input output →
  PhysicalTransportMatrixEntry output input
reverseEntry entry =
  physical-transport-matrix-entry
    (Z3.negateMode (advector entry))
    (reverseResonance entry)

transportEntryCoefficient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  ∀ {input output} →
  PhysicalTransportMatrixEntry input output →
  C3.Complex F
transportEntryCoefficient E velocity {input} entry =
  Coeff.transportCoefficient E input (velocity (advector entry))

reverseEntryCoefficientMeaning :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  ∀ {input output}
    (entry : PhysicalTransportMatrixEntry input output) →
  transportEntryCoefficient E velocity (reverseEntry entry)
  ≡ Coeff.transportCoefficient E output
      (velocity (Z3.negateMode (advector entry)))
reverseEntryCoefficientMeaning E velocity entry = refl

physicalTransportMatrixEntrySkewAdjoint :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  ∀ {input output}
    (entry : PhysicalTransportMatrixEntry input output) →
  C3.complexConjugate
    (transportEntryCoefficient E velocity (reverseEntry entry))
  ≡ C3.complexNegate
      (transportEntryCoefficient E velocity entry)
physicalTransportMatrixEntrySkewAdjoint {E = E}
    velocity reality divergenceFree {input} {output} entry =
  Coeff.physicalVelocityTransportCoefficientSkew
    velocity reality divergenceFree
    (advector entry) input output (resonance entry)

physicalTransportMatrixEntrySkewClosed : Bool
physicalTransportMatrixEntrySkewClosed = true

physicalLowTransportGlobalMatrixSkewAdjointPointwiseConstructed : Bool
physicalLowTransportGlobalMatrixSkewAdjointPointwiseConstructed = true

physicalOddPQBlockToRound35GramConstructed : Bool
physicalOddPQBlockToRound35GramConstructed = false

physicalTransportMatrixEntrySkewClosedIsTrue :
  physicalTransportMatrixEntrySkewClosed ≡ true
physicalTransportMatrixEntrySkewClosedIsTrue = refl

physicalLowTransportGlobalMatrixSkewAdjointPointwiseConstructedIsTrue :
  physicalLowTransportGlobalMatrixSkewAdjointPointwiseConstructed ≡ true
physicalLowTransportGlobalMatrixSkewAdjointPointwiseConstructedIsTrue = refl
