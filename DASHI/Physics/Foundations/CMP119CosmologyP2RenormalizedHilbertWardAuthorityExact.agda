{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact where

------------------------------------------------------------------------
-- R2 SOURCE AUTHORITY IN ITS NATURAL DOMAIN.
--
-- Primary gauge-theory EMT/trace-anomaly results do not state a theorem about
-- an arbitrary CMP119 scalar. They state a Ward/operator identity for the
-- renormalized energy-momentum tensor and the renormalized F^2 operator.
--
-- Local-C already carries the exact applicability witness relevant here:
-- `ShortDistanceAFMatching`, on the SAME continuum family as its local
-- curvature operators and local conserved stress tensor.
--
-- MAX-CUT CORRECTION:
-- once the operator identity has already been proved/stated on that exact
-- Local-C pair, wrapping it as an authority conditional on AF matching is pure
-- compiler work. No second theorem or authority-instantiation leaf survives.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
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

------------------------------------------------------------------------
-- MAX-CUT COMPILER
------------------------------------------------------------------------

fromExactLocalCOperatorIdentity :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian embedding convention
      hilbertTraceNumerator fieldStrengthSquarePolynomial localOperatorNumerator}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian} →
  hilbertTraceNumerator (Local.stressTensor localC)
  ≡
  SU2Trace.realSU2TraceCoefficient embedding convention
  *ℝ
  localOperatorNumerator
    (Local.localOperator localC fieldStrengthSquarePolynomial) →
  RenormalizedHilbertWeylWardAuthority
    localC embedding convention hilbertTraceNumerator
    fieldStrengthSquarePolynomial localOperatorNumerator
fromExactLocalCOperatorIdentity identity = record
  { RenormalizedHilbertWeylWardAuthority.hilbertWeylWardFromAFMatching =
      λ _ → identity
  }

exactOperatorIdentityRoundTripsThroughAuthority :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian embedding convention
      hilbertTraceNumerator fieldStrengthSquarePolynomial localOperatorNumerator}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    (identity :
      hilbertTraceNumerator (Local.stressTensor localC)
      ≡
      SU2Trace.realSU2TraceCoefficient embedding convention
      *ℝ
      localOperatorNumerator
        (Local.localOperator localC fieldStrengthSquarePolynomial)) →
  applyRenormalizedHilbertWeylWard
    (fromExactLocalCOperatorIdentity identity)
  ≡ identity
exactOperatorIdentityRoundTripsThroughAuthority identity = refl

renormalizedHilbertWeylWardAuthorityLevel : ProofLevel
renormalizedHilbertWeylWardAuthorityLevel = standardImported

localCShortDistanceMatchingIsTheApplicabilityWitness : Bool
localCShortDistanceMatchingIsTheApplicabilityWitness = true

noCMP119SpecificTraceScalarWeldRequired : Bool
noCMP119SpecificTraceScalarWeldRequired = true

authorityRecordInstantiationAddsNoMathematics : Bool
authorityRecordInstantiationAddsNoMathematics = true

remainingR2WorkIsInstantiationOfStandardWardAuthority : Bool
remainingR2WorkIsInstantiationOfStandardWardAuthority = false

remainingR2WorkIsExactRenormalizedOperatorIdentity : Bool
remainingR2WorkIsExactRenormalizedOperatorIdentity = true
