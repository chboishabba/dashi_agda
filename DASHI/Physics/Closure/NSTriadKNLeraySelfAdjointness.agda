module DASHI.Physics.Closure.NSTriadKNLeraySelfAdjointness where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean Leray; Marco Cannone; DASHI repository contributors.
-- Title: "Exact Hermitian self-adjointness of the periodic Fourier Leray
-- projector on the Stage-3 C3 carrier".
-- Venue/year: Leray's incompressible projection tradition; Handbook of
-- Mathematical Fluid Dynamics, Volume 3, 2005; DASHI formal development,
-- 2026.
-- DOI: 10.1016/S1874-5792(05)80006-0 for Marco Cannone,
-- "Harmonic Analysis Tools for Solving the Incompressible Navier-Stokes
-- Equations"; Leray's 1934 source has no DOI recorded here.
-- Uses: the exact rank-one projector formula, real Fourier mode vectors,
-- complex conjugation, Hermitian scaling, and additive/subtractive pairing
-- laws.
-- Relationship: proves <P_k u,v> = <u,P_k v> algebraically for the literal
-- repository projector.  It does not assert norm contraction, which belongs
-- to an ordered Euclidean analytic carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive

lerayCoefficient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) → C3.Complex F
lerayCoefficient {F = F} E I k value =
  C3.complexMultiply
    (C3.realEmbed F (C3.inverseNormSquared I k))
    (C3.bilinearDot3 (C3.modeVector E k) value)

lerayRankOneCorrection :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) → C3.Complex3 F
lerayRankOneCorrection E I k value =
  C3.complex3Scale
    (lerayCoefficient E I k value)
    (C3.modeVector E k)

conjugateLerayCoefficient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complexConjugate (lerayCoefficient E I k value)
  ≡
  C3.complexMultiply
    (C3.realEmbed F (C3.inverseNormSquared I k))
    (C3.hermitianPairing3 value (C3.modeVector E k))
conjugateLerayCoefficient {F = F} E I k value =
  trans
    (Hermitian.complexConjugateMultiply
      (C3.realEmbed F (C3.inverseNormSquared I k))
      (C3.bilinearDot3 (C3.modeVector E k) value))
    (Algebra.cong₂ C3.complexMultiply
      (C3.realEmbedConjugate F (C3.inverseNormSquared I k))
      (trans
        (cong C3.complexConjugate
          (sym (Hermitian.realModePairingIsBilinear E k value)))
        (Hermitian.hermitianPairingConjugateSymmetric
          (C3.modeVector E k) value)))

rankOnePairingMovesAcross :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  C3.hermitianPairing3 (lerayRankOneCorrection E I k u) v
  ≡ C3.hermitianPairing3 u (lerayRankOneCorrection E I k v)
rankOnePairingMovesAcross {F = F} E I k u v =
  trans
    (Scaling.hermitianPairingScaleLeft
      (lerayCoefficient E I k u)
      (C3.modeVector E k)
      v)
    (trans
      (Algebra.cong₂ C3.complexMultiply
        (conjugateLerayCoefficient E I k u)
        (Hermitian.realModePairingIsBilinear E k v))
      (trans
        (Scaling.complexMultiplyAssociative
          (C3.realEmbed F (C3.inverseNormSquared I k))
          (C3.hermitianPairing3 u (C3.modeVector E k))
          (C3.bilinearDot3 (C3.modeVector E k) v))
        (trans
          (cong
            (C3.complexMultiply
              (C3.realEmbed F (C3.inverseNormSquared I k)))
            (Algebra.complexMultiplyCommutative
              (C3.hermitianPairing3 u (C3.modeVector E k))
              (C3.bilinearDot3 (C3.modeVector E k) v)))
          (trans
            (sym (Scaling.complexMultiplyAssociative
              (C3.realEmbed F (C3.inverseNormSquared I k))
              (C3.bilinearDot3 (C3.modeVector E k) v)
              (C3.hermitianPairing3 u (C3.modeVector E k))))
            (sym (Scaling.hermitianPairingScaleRight
              (lerayCoefficient E I k v)
              u
              (C3.modeVector E k)))))))

leraySelfAdjoint :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.lerayProject3 E I k u) v
  ≡ C3.hermitianPairing3 u (C3.lerayProject3 E I k v)
leraySelfAdjoint E I k u v =
  trans
    (Additive.hermitianPairingSubtractLeft
      u (lerayRankOneCorrection E I k u) v)
    (trans
      (cong
        (C3.complexSubtract (C3.hermitianPairing3 u v))
        (rankOnePairingMovesAcross E I k u v))
      (sym (Additive.hermitianPairingSubtractRight
        u v (lerayRankOneCorrection E I k v))))

lerayHermitianSelfAdjointnessClosed : Bool
lerayHermitianSelfAdjointnessClosed = true

lerayHermitianSelfAdjointnessClosedIsTrue :
  lerayHermitianSelfAdjointnessClosed ≡ true
lerayHermitianSelfAdjointnessClosedIsTrue = refl
