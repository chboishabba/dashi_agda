module DASHI.Physics.Closure.NSTriadKNLerayAlgebraProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean Leray; Marco Cannone; DASHI repository contributors.
-- Title: "Exact Leray projection algebra and Hermitian self-adjointness
-- boundary for the periodic C3 carrier".
-- Venue/year: Leray's incompressible projection tradition; Handbook of
-- Mathematical Fluid Dynamics, Volume 3, 2005; DASHI development, 2026.
-- DOI: 10.1016/S1874-5792(05)80006-0 for Marco Cannone,
-- "Harmonic Analysis Tools for Solving the Incompressible Navier-Stokes
-- Equations"; Leray's 1934 source has no DOI recorded here.
-- Uses: the exact rank-one Leray formula, real lattice modes, transversality,
-- and the concrete complex zero/scale laws.
-- Relationship: proves that Leray fixes every transverse vector on the exact
-- carrier.  Full Hermitian self-adjointness, projected transversality, and
-- idempotence remain explicit theorem obligations requiring the scale laws and
-- inverse-norm rank-one calculation.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian

lerayFixesTransverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  Helical.Transverse E k value →
  C3.lerayProject3 E I k value ≡ value
lerayFixesTransverse {F = F} E I k value transverse
  rewrite transverse
        | Hermitian.complexMultiplyZeroRight
            (C3.realEmbed F (C3.inverseNormSquared I k))
        | Hermitian.complex3ScaleZero (C3.modeVector E k)
        | Hermitian.complex3SubtractZero value = refl

record LerayHermitianCutset
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set (lsuc r) where
  field
    rankOnePairingMovesAcross :
      ∀ k u v →
      C3.hermitianPairing3
        (C3.complex3Scale
          (C3.complexMultiply
            (C3.realEmbed F (C3.inverseNormSquared I k))
            (C3.bilinearDot3 (C3.modeVector E k) u))
          (C3.modeVector E k))
        v
      ≡
      C3.hermitianPairing3 u
        (C3.complex3Scale
          (C3.complexMultiply
            (C3.realEmbed F (C3.inverseNormSquared I k))
            (C3.bilinearDot3 (C3.modeVector E k) v))
          (C3.modeVector E k))

    leraySelfAdjoint :
      ∀ k u v →
      C3.hermitianPairing3 (C3.lerayProject3 E I k u) v
      ≡ C3.hermitianPairing3 u (C3.lerayProject3 E I k v)

    lerayOutputTransverse :
      ∀ k value → Z3.NonZeroMode k →
      Helical.Transverse E k (C3.lerayProject3 E I k value)

    lerayIdempotent :
      ∀ k value → Z3.NonZeroMode k →
      C3.lerayProject3 E I k (C3.lerayProject3 E I k value)
      ≡ C3.lerayProject3 E I k value

open LerayHermitianCutset public

lerayFixesTransverseClosed : Bool
lerayFixesTransverseClosed = true

lerayFixesTransverseClosedIsTrue : lerayFixesTransverseClosed ≡ true
lerayFixesTransverseClosedIsTrue = refl

leraySelfAdjointnessClosed : Bool
leraySelfAdjointnessClosed = false

leraySelfAdjointnessClosedIsFalse : leraySelfAdjointnessClosed ≡ false
leraySelfAdjointnessClosedIsFalse = refl

lerayIdempotenceClosed : Bool
lerayIdempotenceClosed = false

lerayIdempotenceClosedIsFalse : lerayIdempotenceClosed ≡ false
lerayIdempotenceClosedIsFalse = refl
