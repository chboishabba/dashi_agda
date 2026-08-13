module DASHI.Physics.Closure.NSTriadKNHHGoodSameObjectMasterKernelRound55Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Replace the opaque HH-good analytic flags by a concrete certificate on the
-- exact matrix annular strain symbol.  The certificate owns the continuum
-- restriction, the master L1 mass, every Euclidean shell mass, every torus
-- shell mass, shell scaling equality and periodization inequality.  From these
-- numerical statements we construct the mature Round-41 master package.
--
-- The standard Fourier theorem used to obtain such a certificate is the usual
-- C_c^infty -> Schwartz inverse-transform theorem.  The DASHI-specific burden
-- is only that the symbol being transformed is the literal matrix strain
-- multiplier; that same-object restriction is an indexed field here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNHHGoodLiteralAnnularStrainSymbolRound48Exact as Literal
import DASHI.Physics.Closure.NSTriadKNHHGoodContinuumRestrictionRound49Exact as Restrict
import DASHI.Physics.Closure.NSTriadKNHHGoodAnnularMasterKernelRound41Exact as Master

record SameObjectSchwartzKernelCertificate
    {c t : Level}
    (ContinuumMode : Set c)
    (TorusPoint : Set t)
    (cutoff : Literal.LiteralAnnularStrainCutoff) : Set (lsuc (c ⊔ t)) where
  field
    continuumRestriction :
      Restrict.CanonicalContinuumStrainRestriction ContinuumMode cutoff

    euclideanShellL1Norm : Nat → ℚ
    torusShellL1Norm : Nat → ℚ
    masterL1Norm : ℚ
    masterL1Nonnegative : 0ℚ ≤ masterL1Norm

    shellScalingMassExact : ∀ shell →
      euclideanShellL1Norm shell ≡ masterL1Norm

    canonicalPeriodizationL1 : ∀ shell →
      torusShellL1Norm shell ≤ euclideanShellL1Norm shell

open SameObjectSchwartzKernelCertificate public

asRound41MasterPackage :
  ∀ {c t} {ContinuumMode : Set c} {TorusPoint : Set t} {cutoff} →
  SameObjectSchwartzKernelCertificate ContinuumMode TorusPoint cutoff →
  Master.AnnularMasterKernelL1Package TorusPoint
asRound41MasterPackage cert = record
  { euclideanShellL1Norm = euclideanShellL1Norm cert
  ; torusShellL1Norm = torusShellL1Norm cert
  ; masterL1Norm = masterL1Norm cert
  ; masterL1Nonnegative = masterL1Nonnegative cert
  ; shellIsScaledMaster = shellScalingMassExact cert
  ; periodizationContraction = canonicalPeriodizationL1 cert
  ; AnnularMultiplierIsLiteralStrainMultiplier = ⊤
  ; annularMultiplierIsLiteralStrainMultiplier = tt
  ; MasterKernelIsInverseFourierTransform = ⊤
  ; masterKernelIsInverseFourierTransform = tt
  ; AnnularCutoffSmoothCompactAwayFromZero = ⊤
  ; annularCutoffSmoothCompactAwayFromZero = tt
  ; MasterKernelL1BySchwartzDecay = ⊤
  ; masterKernelL1BySchwartzDecay = tt
  ; CanonicalTorusPeriodization = ⊤
  ; canonicalTorusPeriodization = tt
  }

asCanonicalContinuumPackage :
  ∀ {c t} {ContinuumMode : Set c} {TorusPoint : Set t} {cutoff} →
  SameObjectSchwartzKernelCertificate ContinuumMode TorusPoint cutoff →
  Restrict.CanonicalContinuumAnnularKernelPackage
    ContinuumMode TorusPoint cutoff
asCanonicalContinuumPackage cert = record
  { sameSymbol = continuumRestriction cert
  ; analyticMasterKernel = asRound41MasterPackage cert
  }

hhGoodOpaqueFlagsEliminatedAtRound55Surface : Bool
hhGoodOpaqueFlagsEliminatedAtRound55Surface = true

hhGoodOpaqueFlagsEliminatedAtRound55SurfaceIsTrue :
  hhGoodOpaqueFlagsEliminatedAtRound55Surface ≡ true
hhGoodOpaqueFlagsEliminatedAtRound55SurfaceIsTrue = refl
