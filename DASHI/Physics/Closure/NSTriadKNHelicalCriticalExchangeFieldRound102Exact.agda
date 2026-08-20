module DASHI.Physics.Closure.NSTriadKNHelicalCriticalExchangeFieldRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: Zhen Lei; Fang-Hua Lin; Yi Zhou.
-- Title: "Structure of Helicity and Global Solutions of Incompressible
-- Navier-Stokes Equation".
-- DOI: 10.1007/s00205-015-0884-8.
--
-- ROUND102 / REALFIELD HELICAL CRITICAL EXCHANGE
--
-- Source-native lifting of the rational Round102 helical reduction to the
-- arbitrary RealField carrier used by the literal periodic Fourier modules.
-- If nonlinear helicity conservation identifies the plus/minus critical-energy
-- tangents, then unsigned critical production is exactly twice either sector
-- tangent.  If either opposite sector is absent, homochiral critical production
-- vanishes exactly.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

private
  two : ∀ {r : Level} (F : C3.RealField r) → C3.Carrier F
  two F = C3.add F (C3.one F) (C3.one F)

record HelicalCriticalFieldTangent {r : Level} (F : C3.RealField r) : Set r where
  constructor helical-critical-field-tangent
  field
    plusTangent minusTangent : C3.Carrier F

open HelicalCriticalFieldTangent public

unsignedCriticalTangent :
  ∀ {r} {F : C3.RealField r} →
  HelicalCriticalFieldTangent F → C3.Carrier F
unsignedCriticalTangent {F = F} D =
  C3.add F (plusTangent D) (minusTangent D)

signedHelicityTangent :
  ∀ {r} {F : C3.RealField r} →
  HelicalCriticalFieldTangent F → C3.Carrier F
signedHelicityTangent {F = F} D =
  C3.add F (plusTangent D) (C3.negate F (minusTangent D))

nonlinearHelicityConserved :
  ∀ {r} {F : C3.RealField r} →
  HelicalCriticalFieldTangent F → Set r
nonlinearHelicityConserved D = plusTangent D ≡ minusTangent D

helicityConservationKillsSignedTangent :
  ∀ {r} {F : C3.RealField r}
    (D : HelicalCriticalFieldTangent F) →
  nonlinearHelicityConserved D →
  signedHelicityTangent D ≡ C3.zero F
helicityConservationKillsSignedTangent {F = F} D conserved
  rewrite conserved =
  P.R.solve 1
    (λ m → (m P.R.⊕ P.R.⊝ m) P.R.⊜ P.R.K (C3.zero F))
    refl
    (minusTangent D)
  where module P = Field.Polynomial F

criticalProductionIsTwiceExchange :
  ∀ {r} {F : C3.RealField r}
    (D : HelicalCriticalFieldTangent F) →
  nonlinearHelicityConserved D →
  unsignedCriticalTangent D
  ≡ C3.multiply F (two F) (minusTangent D)
criticalProductionIsTwiceExchange {F = F} D conserved
  rewrite conserved =
  P.R.solve 1
    (λ m →
      (m P.R.⊕ m)
      P.R.⊜
      ((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F)) P.R.⊗ m))
    refl
    (minusTangent D)
  where module P = Field.Polynomial F

homochiralProductionVanishes :
  ∀ {r} {F : C3.RealField r}
    (D : HelicalCriticalFieldTangent F) →
  nonlinearHelicityConserved D →
  minusTangent D ≡ C3.zero F →
  unsignedCriticalTangent D ≡ C3.zero F
homochiralProductionVanishes {F = F} D conserved absent
  rewrite criticalProductionIsTwiceExchange D conserved
        | absent =
  P.R.solve 0
    ((P.R.K (two F) P.R.⊗ P.R.K (C3.zero F))
      P.R.⊜ P.R.K (C3.zero F))
    refl
  where module P = Field.Polynomial F

round102RealFieldHelicalCriticalExchangeReductionClosed : Bool
round102RealFieldHelicalCriticalExchangeReductionClosed = true

round102RealFieldHelicalCriticalExchangeReductionClosedIsTrue :
  round102RealFieldHelicalCriticalExchangeReductionClosed ≡ true
round102RealFieldHelicalCriticalExchangeReductionClosedIsTrue = refl
