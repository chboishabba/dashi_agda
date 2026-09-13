module DASHI.Analysis.RiemannG2LiteralCellIntegralUpperExact where

------------------------------------------------------------------------
-- PAIR-SPECIFIC INTEGRAL MAJORANTS -> LITERAL CELL UPPERS
--
-- The RH consumer does not require a global integration theory or a particular
-- quadrature algorithm.  For each literal zero cell it needs only:
--
--   literal integrand <= majorant                       (pointwise)
--   that pointwise proof -> integral literal <= integral majorant
--   integral majorant <= cellUpper                     (backend certificate)
--
-- The second arrow is deliberately pair-specific: requiring monotonicity for
-- every function pair would inflate the RH hypotheses.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal
import DASHI.Analysis.RiemannG2LiteralCellwiseNearUpperExact as Cellwise

literalIntegrand :
  forall {S transport offInput} ->
  (kernel : Literal.FinalNearLiteralKernel
    {S = S} {transport = transport} offInput) ->
  Literal.ZeroIndex kernel ->
  NearFar.Scalar S ->
  NearFar.Scalar S
literalIntegrand kernel sigma u =
  Literal.mul kernel
    (Literal.mul kernel
      (Literal.mul kernel (Literal.four kernel) (Literal.poleTaperValue kernel u))
      (Literal.mul kernel
        (Literal.multiplicity kernel sigma)
        (Literal.cosh kernel
          (Literal.mul kernel
            (Literal.horizontalDisplacement kernel sigma) u))))
    (Literal.cos kernel
      (Literal.mul kernel (Literal.targetRelativeGap kernel sigma) u))

record LiteralCellIntegralUpperAuthority
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (kernel : Literal.FinalNearLiteralKernel offInput) : Set₁ where
  field
    majorant :
      Literal.ZeroIndex kernel -> NearFar.Scalar S -> NearFar.Scalar S

    cellUpper : Literal.ZeroIndex kernel -> NearFar.Scalar S

    literalIntegrandBelowMajorant :
      (sigma : Literal.ZeroIndex kernel) ->
      (u : NearFar.Scalar S) ->
      NearFar._≤_ S
        (literalIntegrand kernel sigma u)
        (majorant sigma u)

    integrateMonotoneForMajorant :
      (sigma : Literal.ZeroIndex kernel) ->
      ((u : NearFar.Scalar S) ->
        NearFar._≤_ S
          (literalIntegrand kernel sigma u)
          (majorant sigma u)) ->
      NearFar._≤_ S
        (Literal.integrate kernel (literalIntegrand kernel sigma))
        (Literal.integrate kernel (majorant sigma))

    integratedMajorantBelowUpper :
      (sigma : Literal.ZeroIndex kernel) ->
      NearFar._≤_ S
        (Literal.integrate kernel (majorant sigma))
        (cellUpper sigma)

    authorityReference : String

open LiteralCellIntegralUpperAuthority public

literalCellBelowIntegralUpper :
  forall {S transport offInput kernel} ->
  (authority : LiteralCellIntegralUpperAuthority
    {S = S} {transport = transport} offInput kernel) ->
  (sigma : Literal.ZeroIndex kernel) ->
  NearFar._≤_ S
    (Literal.cellResponse kernel sigma)
    (cellUpper authority sigma)
literalCellBelowIntegralUpper
    {S = S} {kernel = kernel} authority sigma =
  subst
    (λ exactCell -> NearFar._≤_ S exactCell (cellUpper authority sigma))
    (sym (Literal.cellResponseIsLiteralReflectionPair kernel sigma))
    (NearFar.≤-trans S
      (integrateMonotoneForMajorant authority sigma
        (literalIntegrandBelowMajorant authority sigma))
      (integratedMajorantBelowUpper authority sigma))

compileIntegralAuthorityToCellwiseUpper :
  forall {S transport offInput kernel} ->
  (enumeration : Cellwise.LiteralNearEnumeration
    {S = S} {transport = transport} offInput kernel) ->
  (authority : LiteralCellIntegralUpperAuthority offInput kernel) ->
  Cellwise.LiteralCellwiseUpper offInput kernel enumeration
compileIntegralAuthorityToCellwiseUpper enumeration authority = record
  { Cellwise.cellUpper = cellUpper authority
  ; Cellwise.literalCellBelowUpper = literalCellBelowIntegralUpper authority
  ; Cellwise.upperReference = authorityReference authority
  }

record LiteralCellIntegralUpperBoundary : Set where
  constructor literal-cell-integral-upper-boundary
  field
    specificQuadratureAlgorithmRequiredByRH : Bool
    specificQuadratureAlgorithmRequiredByRHIsFalse :
      specificQuadratureAlgorithmRequiredByRH ≡ false

    globalIntegrationMonotonicityRequiredByRH : Bool
    globalIntegrationMonotonicityRequiredByRHIsFalse :
      globalIntegrationMonotonicityRequiredByRH ≡ false

    pairSpecificMajorantTransportSuffices : Bool
    pairSpecificMajorantTransportSufficesIsTrue :
      pairSpecificMajorantTransportSuffices ≡ true

    exactTranscendentalIntegralEqualityRequired : Bool
    exactTranscendentalIntegralEqualityRequiredIsFalse :
      exactTranscendentalIntegralEqualityRequired ≡ false

    backendStillMustProveIntegratedMajorantUpper : Bool
    backendStillMustProveIntegratedMajorantUpperIsTrue :
      backendStillMustProveIntegratedMajorantUpper ≡ true

    strictClusterResponseMarginPaidHere : Bool
    strictClusterResponseMarginPaidHereIsFalse :
      strictClusterResponseMarginPaidHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalLiteralCellIntegralUpperBoundary : LiteralCellIntegralUpperBoundary
canonicalLiteralCellIntegralUpperBoundary =
  literal-cell-integral-upper-boundary
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "Do not make a global integration theory or one quadrature implementation a Clay prerequisite. For each literal reflection-paired cell, provide a pointwise majorant, only the monotonicity transport for that exact integrand/majorant pair, and a certified upper on the majorant integral. This compiles the one-sided cell upper consumed by the finite cellwise route. The actual backend certificate and downstream strict ClusterResponse margin remain theorem-bearing obligations; RH is not derived here."
