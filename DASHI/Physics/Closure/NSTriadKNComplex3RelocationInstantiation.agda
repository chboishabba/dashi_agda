module DASHI.Physics.Closure.NSTriadKNComplex3RelocationInstantiation where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Concrete C3 instantiation of resonant derivative relocation".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a repository-original algebraic theorem.
-- Uses: the exact integer Fourier lattice, mode-vector additivity,
-- bilinear-dot right-linearity and symmetry, and the generic
-- resonant-transverse relocation theorem.
-- Relationship: closes u_p dot q = u_p dot k on the literal complex carrier.
-- It does not assert a first-partial-adjoint high-high-to-low estimate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHighHighToLowCancellationProgram as Cancellation

complex3RelocationLaws :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) →
  Cancellation.ResonantTransverseRelocationLaws {m = lzero} {v = r} {s = r}
complex3RelocationLaws F E = record
  { Mode = Z3.FourierMode
  ; Vector = C3.Complex3 F
  ; Scalar = C3.Complex F
  ; addMode = Z3.addMode
  ; modeVector = C3.modeVector E
  ; vectorAdd = C3.complex3Add
  ; dot = C3.bilinearDot3
  ; scalarAdd = C3.complexAdd
  ; zero = C3.complexZero F
  ; modeVectorAdd = Algebra.modeVectorAdd E
  ; dotRightAdd = Algebra.bilinearDot3RightAdd
  ; scalarZeroLeft = Algebra.complexAddZeroLeft
  }

transverseRightOrientation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (mode : Z3.FourierMode)
    (value : C3.Complex3 F) →
  Helical.Transverse E mode value →
  C3.bilinearDot3 value (C3.modeVector E mode)
  ≡ C3.complexZero F
transverseRightOrientation E mode value transverse =
  trans
    (Algebra.bilinearDot3Commutative value (C3.modeVector E mode))
    transverse

complex3OutputDerivativeRelocation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode}
    {uP : C3.Complex3 F} →
  Z3.Resonance p q k →
  Helical.Transverse E p uP →
  C3.bilinearDot3 uP (C3.modeVector E q)
  ≡
  C3.bilinearDot3 uP (C3.modeVector E k)
complex3OutputDerivativeRelocation {F = F} E {p} {q} {k} {uP}
  resonance transverse =
  Cancellation.outputDerivativeRelocation
    (complex3RelocationLaws F E)
    k p q uP
    (Z3.Resonance.closes resonance)
    (transverseRightOrientation E p uP transverse)

concreteComplexCarrierOutputRelocationClosed : Bool
concreteComplexCarrierOutputRelocationClosed = true

concreteComplexCarrierOutputRelocationClosedIsTrue :
  concreteComplexCarrierOutputRelocationClosed ≡ true
concreteComplexCarrierOutputRelocationClosedIsTrue = refl
