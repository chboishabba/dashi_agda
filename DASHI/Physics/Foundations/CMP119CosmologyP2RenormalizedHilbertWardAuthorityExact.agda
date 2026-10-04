{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact where

------------------------------------------------------------------------
-- R2 SOURCE AUTHORITY IN ITS NATURAL DOMAIN.
--
-- Primary gauge-theory EMT/trace-anomaly results do not state a theorem about
-- an arbitrary CMP119 scalar.  They state a Ward/operator identity for the
-- renormalized energy-momentum tensor and the renormalized F^2 operator.
--
-- Local-C already carries the exact applicability witness relevant here:
-- `ShortDistanceAFMatching`, on the SAME continuum family as its local
-- curvature operators and local conserved stress tensor.  Therefore expose the
-- imported theorem as a function of that matching witness.  Applying it to a
-- Local-C package uses `shortDistanceAFMatching` directly; no independent
-- "selected trace = renormalized trace" scalar weld is required.
--
-- Authorities/calibration:
--   Collins--Duncan--Joglekar, Phys. Rev. D 16 (1977) 438,
--     DOI 10.1103/PhysRevD.16.438.
--   N. K. Nielsen, Nucl. Phys. B 120 (1977) 212,
--     DOI 10.1016/0550-3213(77)90040-2.
--   K. Fujikawa, Phys. Rev. D 23 (1981) 2262,
--     DOI 10.1103/PhysRevD.23.2262.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

traceAnomalyWardPrimaryDOI : String
traceAnomalyWardPrimaryDOI = "10.1103/PhysRevD.16.438"

nonAbelianEMTPrimaryDOI : String
nonAbelianEMTPrimaryDOI = "10.1016/0550-3213(77)90040-2"

gravitationalSourceEMTDOI : String
gravitationalSourceEMTDOI = "10.1103/PhysRevD.23.2262"

record RenormalizedHilbertWeylWardAuthority
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    (localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : SU2Trace.RealSU2TraceConvention embedding)
    (hilbertTraceNumerator : StressTensor → ℝ)
    (fieldStrengthSquarePolynomial : CurvaturePolynomial)
    (localOperatorNumerator : LocalOperator → ℝ)
    : Set₁ where
  field
    -- Standard renormalized Weyl/Callan--Symanzik identity, formulated on the
    -- exact operator pair to which it is applied.  Local-C's AF matching is the
    -- applicability witness, rather than a post-hoc scalar identification.
    hilbertWeylWardFromAFMatching :
      Local.ShortDistanceAFMatching localC →
      hilbertTraceNumerator (Local.stressTensor localC)
      ≡
      SU2Trace.realSU2TraceCoefficient embedding convention
      *ℝ
      localOperatorNumerator
        (Local.localOperator localC fieldStrengthSquarePolynomial)

open RenormalizedHilbertWeylWardAuthority public

applyRenormalizedHilbertWeylWard :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian embedding convention
      hilbertTraceNumerator fieldStrengthSquarePolynomial localOperatorNumerator}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian} →
  RenormalizedHilbertWeylWardAuthority
    localC embedding convention hilbertTraceNumerator
    fieldStrengthSquarePolynomial localOperatorNumerator →
  hilbertTraceNumerator (Local.stressTensor localC)
  ≡
  SU2Trace.realSU2TraceCoefficient embedding convention
  *ℝ
  localOperatorNumerator
    (Local.localOperator localC fieldStrengthSquarePolynomial)
applyRenormalizedHilbertWeylWard {localC = localC} authority =
  hilbertWeylWardFromAFMatching authority
    (Local.shortDistanceAFMatching localC)

renormalizedHilbertWeylWardAuthorityLevel : ProofLevel
renormalizedHilbertWeylWardAuthorityLevel = standardImported

localCShortDistanceMatchingIsTheApplicabilityWitness : Bool
localCShortDistanceMatchingIsTheApplicabilityWitness = true

noCMP119SpecificTraceScalarWeldRequired : Bool
noCMP119SpecificTraceScalarWeldRequired = true

remainingR2WorkIsInstantiationOfStandardWardAuthority : Bool
remainingR2WorkIsInstantiationOfStandardWardAuthority = true
