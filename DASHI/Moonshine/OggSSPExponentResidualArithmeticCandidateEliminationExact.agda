module DASHI.Moonshine.OggSSPExponentResidualArithmeticCandidateEliminationExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC ARITHMETIC SOURCE CANDIDATE ELIMINATION
--
-- ATTRIBUTION / AUTHORITY BOUNDARY
--
-- External/source-calibrated inputs reused:
--
--   * p=2 spinor representation dimension = 2
--     from AllPrimeRepresentationFrickeClosureExact;
--   * p=3 supersingular Frobenius orbit count = 1
--     from OggSSPExponentResidualVsSupersingularOrbitSeparationExact;
--   * exceptional monstrous-exponent residuals R2=10, R3=2
--     from the attributed Duncan--Swisher arithmetic lane.
--
-- DASHI contribution:
-- reject two tempting but insufficient source proxies at the pi0 gate.
--
-- This does NOT prove that no arithmetic source groupoid exists.  It proves
-- only that these two obvious proxies cannot be the required residual source.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact as Spinor
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.OggSSPExponentResidualVsSupersingularOrbitSeparationExact as Separation
import DASHI.Moonshine.OggSSPExponentResidualArithmeticSourceInterfaceExact as Source
import DASHI.Moonshine.OggSSPArithmeticResidualGroupoidRecognitionFunctorExact as Recognition

------------------------------------------------------------------------
-- 1. p=2: a bare two-dimensional spinor basis cannot itself be the
--    ten-component exceptional residual groupoid under identity-only semantics.
------------------------------------------------------------------------

p2SpinorDimension :
  Nat
p2SpinorDimension =
  Spinor.spinorPrime2Dimension

p2SpinorDimensionIsTwo :
  p2SpinorDimension ≡ 2
p2SpinorDimensionIsTwo =
  Spinor.spinorPrime2DimensionIsTwo

p2ExpectedResidualIsTen :
  Source.expectedResidualCount Source.residualP2 ≡ 10
p2ExpectedResidualIsTen =
  Source.p2ExpectedResidualIsTen

record P2SpinorBasisIdentityProxy : Set where
  constructor p2-spinor-basis-identity-proxy
  field
    basisStateCount : Nat
    basisStateCountIsSpinorDimension :
      basisStateCount ≡ p2SpinorDimension

canonicalP2SpinorBasisIdentityProxy :
  P2SpinorBasisIdentityProxy
canonicalP2SpinorBasisIdentityProxy =
  p2-spinor-basis-identity-proxy
    p2SpinorDimension
    refl

p2SpinorBasisIdentityPi0Count :
  P2SpinorBasisIdentityProxy ->
  Nat
p2SpinorBasisIdentityPi0Count proxy =
  P2SpinorBasisIdentityProxy.basisStateCount proxy

p2CanonicalSpinorProxyPi0IsTwo :
  p2SpinorBasisIdentityPi0Count canonicalP2SpinorBasisIdentityProxy
  ≡ 2
p2CanonicalSpinorProxyPi0IsTwo =
  p2SpinorDimensionIsTwo

p2SpinorBasisIdentityProxyFailsResidualPi0 :
  Recognition.Pi0RecognitionGate
    (Source.expectedResidualCount Source.residualP2)
    (p2SpinorBasisIdentityPi0Count canonicalP2SpinorBasisIdentityProxy)
  ->
  ⊥
p2SpinorBasisIdentityProxyFailsResidualPi0 ()

------------------------------------------------------------------------
-- 2. p=3: the existing supersingular Frobenius orbit spectrum has one
--    component, so it cannot be the two-component exponent residual source.
------------------------------------------------------------------------

p3SupersingularFrobeniusPi0 :
  Separation.supersingularPi0Count Matrix.prime3
  ≡ 1
p3SupersingularFrobeniusPi0 =
  Separation.p3SupersingularPi0IsOne

p3ExpectedResidualIsTwo :
  Source.expectedResidualCount Source.residualP3 ≡ 2
p3ExpectedResidualIsTwo =
  Source.p3ExpectedResidualIsTwo

p3SupersingularFrobeniusProxyFailsResidualPi0 :
  Separation.supersingularPi0Count Matrix.prime3
  ≡ Source.expectedResidualCount Source.residualP3
  ->
  ⊥
p3SupersingularFrobeniusProxyFailsResidualPi0 =
  Separation.p3SupersingularPi0IsNotExponentResidual

------------------------------------------------------------------------
-- 3. Candidate taxonomy.
------------------------------------------------------------------------

data ArithmeticResidualSourceCandidate : Set where
  p2SpinorBasisIdentityProxy : ArithmeticResidualSourceCandidate
  p3SupersingularFrobeniusProxy : ArithmeticResidualSourceCandidate
  genuineExternallyJustifiedResidualGroupoid : ArithmeticResidualSourceCandidate

data CandidateEliminatedAtPi0 :
  ArithmeticResidualSourceCandidate ->
  Set where
  eliminateP2SpinorBasis :
    CandidateEliminatedAtPi0 p2SpinorBasisIdentityProxy
  eliminateP3SupersingularFrobenius :
    CandidateEliminatedAtPi0 p3SupersingularFrobeniusProxy

p2SpinorProxyEliminated :
  CandidateEliminatedAtPi0 p2SpinorBasisIdentityProxy
p2SpinorProxyEliminated =
  eliminateP2SpinorBasis

p3SupersingularProxyEliminated :
  CandidateEliminatedAtPi0 p3SupersingularFrobeniusProxy
p3SupersingularProxyEliminated =
  eliminateP3SupersingularFrobenius

data GenuineArithmeticResidualSourceConstructedHere : Set where

genuineArithmeticResidualSourceStillOpen :
  GenuineArithmeticResidualSourceConstructedHere -> ⊥
genuineArithmeticResidualSourceStillOpen ()

record ArithmeticResidualCandidateEliminationBoundary : Set where
  constructor arithmetic-residual-candidate-elimination-boundary
  field
    p2SpinorDimensionTwoReused : Bool
    p2SpinorIdentityProxyPi0Two : Bool
    p2SpinorIdentityProxyRejectedAgainstResidualTen : Bool
    p3SupersingularPi0OneReused : Bool
    p3SupersingularProxyRejectedAgainstResidualTwo : Bool
    rejectedProxyMeansNoArithmeticSourceCanExist : Bool
    genuineArithmeticResidualSourceConstructed : Bool

canonicalArithmeticResidualCandidateEliminationBoundary :
  ArithmeticResidualCandidateEliminationBoundary
canonicalArithmeticResidualCandidateEliminationBoundary =
  arithmetic-residual-candidate-elimination-boundary
    true true true true true
    false false
