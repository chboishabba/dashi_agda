module DASHI.Moonshine.JInvariantEisensteinInternalDivisorPowerKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_≤_)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumBoundExact as DivisorBound
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantEisensteinDivisorPowerSourceAtlasExact as SourceAtlas

------------------------------------------------------------------------
-- INTERNAL DIVISOR-POWER INSTANTIATION OF THE EXISTING FINITE E4/E6 OWNER
--
-- The existing recurrence remains the canonical consumer.  This module only
-- pays its DivisorPowerKernel parameter from repo-owned finite arithmetic.
-- Classical source context and OEIS parity remain separate from the executable
-- definition.
------------------------------------------------------------------------

internalDivisorPowerKernel : Series.DivisorPowerKernel
internalDivisorPowerKernel = Divisor.canonicalDivisorPowerKernel

------------------------------------------------------------------------
-- The canonical kernel now carries exact finite polynomial envelopes as well.
-- These are inherited from the shared oneTo/divisor-filter proof; they do not
-- rely on OEIS or analytic asymptotics.
------------------------------------------------------------------------

internalSigma3QuarticBound :
  (n : Nat) ->
  Series.sigma3 internalDivisorPowerKernel n
  ≤ Divisor.powNat n 3 * n
internalSigma3QuarticBound = DivisorBound.sigma3QuarticBound

internalSigma5SexticBound :
  (n : Nat) ->
  Series.sigma5 internalDivisorPowerKernel n
  ≤ Divisor.powNat n 5 * n
internalSigma5SexticBound = DivisorBound.sigma5SexticBound

e4Internal :
  (C : Complex.ConstructedComplexPackage) ->
  Nat ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
e4Internal C terms tau =
  Series.e4Truncated C internalDivisorPowerKernel terms tau

e6Internal :
  (C : Complex.ConstructedComplexPackage) ->
  Nat ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
e6Internal C terms tau =
  Series.e6Truncated C internalDivisorPowerKernel terms tau

discriminantNumeratorInternal :
  (C : Complex.ConstructedComplexPackage) ->
  Nat ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
discriminantNumeratorInternal C terms tau =
  Series.discriminantNumeratorTruncated
    C internalDivisorPowerKernel terms tau

record InternalEisensteinKernelBoundary : Set where
  constructor internal-eisenstein-kernel-boundary
  field
    existingFiniteRecurrenceReused : Bool
    positiveDivisorScannerReused : Bool
    sigma3ExecutableInternally : Bool
    sigma5ExecutableInternally : Bool
    divisorPowerKernelExternalOnInternalRoute : Bool
    classicalSourceAtlasRetained : Bool
    oeisParityRetainedAsNonAuthority : Bool
    finiteEqualsInfiniteAnalyticEisenstein : Bool
    finiteArithmeticCreatesModularity : Bool
    reading : String
open InternalEisensteinKernelBoundary public

canonicalInternalEisensteinKernelBoundary : InternalEisensteinKernelBoundary
canonicalInternalEisensteinKernelBoundary =
  internal-eisenstein-kernel-boundary
    true true true true
    false
    true true
    false false
    "the existing finite E4/E6 recurrence is now inhabited by repo-owned sigma3/sigma5 arithmetic with exact polynomial growth envelopes; source attribution and OEIS parity remain separate, and the finite-to-infinite analytic/modularity boundary is unchanged"

------------------------------------------------------------------------
-- Retain the explicit source/parity split in the typechecked dependency graph.
------------------------------------------------------------------------

sourceAtlasIsNonPromoting :
  SourceAtlas.citationsCreateAuthority
    SourceAtlas.canonicalEisensteinDivisorPowerAttributionBoundary
  ≡ false
sourceAtlasIsNonPromoting = refl
