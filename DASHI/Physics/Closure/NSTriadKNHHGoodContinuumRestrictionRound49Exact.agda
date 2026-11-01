module DASHI.Physics.Closure.NSTriadKNHHGoodContinuumRestrictionRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler Equations".
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Separate the remaining HH-good Fourier seam into two logically distinct
-- statements.  A is the same-object theorem: the smooth continuum matrix
-- multiplier used for Fourier inversion restricts to the literal Round-48
-- lattice strain symbol.  B is the standard analytic master-kernel theorem:
-- smooth compact annular support gives a Schwartz/L1 inverse Fourier kernel,
-- scale-invariant L1 mass, and canonical torus periodization.
--
-- Only A is a DASHI provenance obligation.  B remains an explicit standard
-- Fourier-analysis authority and is not confused with the same-object bridge.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNHHGoodLiteralAnnularStrainSymbolRound48Exact as Literal
import DASHI.Physics.Closure.NSTriadKNHHGoodAnnularMasterKernelRound41Exact as Master
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized

record CanonicalContinuumStrainRestriction
    {c : Level}
    (ContinuumMode : Set c)
    (cutoff : Literal.LiteralAnnularStrainCutoff) : Set (lsuc c) where
  field
    embedProjectionMode : V.ProjectionMode → ContinuumMode
    continuumVorticity : Set c
    embedVorticity : V.Vec3 → continuumVorticity

    continuumAnnularStrainSymbol :
      ContinuumMode → continuumVorticity → Matrix.Matrix3

    continuumSymbolRestrictsToLiteralPhysicalSymbol :
      ∀ modeData omega →
      continuumAnnularStrainSymbol
        (embedProjectionMode modeData)
        (embedVorticity omega)
      ≡ Literal.literalAnnularStrainSymbol cutoff modeData omega

open CanonicalContinuumStrainRestriction public

record CanonicalContinuumAnnularKernelPackage
    {c t : Level}
    (ContinuumMode : Set c)
    (TorusPoint : Set t)
    (cutoff : Literal.LiteralAnnularStrainCutoff) : Set (lsuc (c ⊔ t)) where
  field
    sameSymbol : CanonicalContinuumStrainRestriction ContinuumMode cutoff

    -- Standard analytic authority for THIS continuum symbol.
    analyticMasterKernel : Master.AnnularMasterKernelL1Package TorusPoint

open CanonicalContinuumAnnularKernelPackage public

periodizedAnnularStrainKernelFromCanonicalPackage :
  ∀ {c t} {ContinuumMode : Set c} {TorusPoint : Set t} {cutoff} →
  CanonicalContinuumAnnularKernelPackage ContinuumMode TorusPoint cutoff →
  Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint
periodizedAnnularStrainKernelFromCanonicalPackage package =
  Master.round40KernelTheoremFromMasterPackage
    (analyticMasterKernel package)

canonicalContinuumRestrictionMakesSameObjectSeamExplicit : Bool
canonicalContinuumRestrictionMakesSameObjectSeamExplicit = true

physicalCanonicalContinuumStrainRestrictionConstructed : Bool
physicalCanonicalContinuumStrainRestrictionConstructed = false

standardAnalyticMasterKernelForLiteralSymbolConstructed : Bool
standardAnalyticMasterKernelForLiteralSymbolConstructed = false

canonicalContinuumRestrictionMakesSameObjectSeamExplicitIsTrue :
  canonicalContinuumRestrictionMakesSameObjectSeamExplicit ≡ true
canonicalContinuumRestrictionMakesSameObjectSeamExplicitIsTrue = refl

physicalCanonicalContinuumStrainRestrictionConstructedIsFalse :
  physicalCanonicalContinuumStrainRestrictionConstructed ≡ false
physicalCanonicalContinuumStrainRestrictionConstructedIsFalse = refl

standardAnalyticMasterKernelForLiteralSymbolConstructedIsFalse :
  standardAnalyticMasterKernelForLiteralSymbolConstructed ≡ false
standardAnalyticMasterKernelForLiteralSymbolConstructedIsFalse = refl
