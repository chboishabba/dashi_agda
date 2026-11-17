module DASHI.Physics.CondensedMatter.MATBGTHFSourceFaithfulDiscretizationObligationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- THF SOURCE-FAITHFUL DISCRETIZATION OBLIGATION
--
-- Xiao et al. explicitly supply the continuous density measure d^2 k / A_BZ.
-- That pays the continuum normalization. It does not uniquely select a finite
-- reciprocal-space domain, mesh/quadrature, ultraviolet cutoff, convergence
-- tolerance, or identify the displayed self-consistency symbol V with the
-- parameter-list symbol Y. Those are separate numerical/source-identity
-- obligations and must not be hidden inside a generic "normalization" TODO.
------------------------------------------------------------------------

record THFContinuousMeasureReceipt : Set where
  constructor thf-continuous-measure-receipt
  field
    sourceDOI : String
    continuousMeasure : String
    spinValleyPrefactor : String
    continuumNormalizationSourcePaid : Bool

open THFContinuousMeasureReceipt public

canonicalTHFContinuousMeasureReceipt : THFContinuousMeasureReceipt
canonicalTHFContinuousMeasureReceipt =
  thf-continuous-measure-receipt
    "10.1038/s41586-026-10378-x"
    "integral d^2 k / A_BZ"
    "4"
    true

record THFDiscreteProducerObligation : Set where
  constructor thf-discrete-producer-obligation
  field
    finiteBZDomainSpecified : Bool
    reciprocalMeshSpecified : Bool
    quadratureWeightsSpecified : Bool
    ultravioletCutoffSpecified : Bool
    convergenceToleranceSpecified : Bool
    sourceIdentityVEqualsYSpecified : Bool
    sourceFaithfulSelfConsistentSolvePaid : Bool

open THFDiscreteProducerObligation public

currentTHFDiscreteProducerObligation : THFDiscreteProducerObligation
currentTHFDiscreteProducerObligation =
  thf-discrete-producer-obligation
    false false false false false false false

record THFDiscretizationBoundary : Set where
  constructor thf-discretization-boundary
  field
    continuousMeasureIsNotMissing : Bool
    continuumMeasureDoesNotSelectDiscreteMesh : Bool
    arbitraryCutoffDoesNotBecomeSourceCalibration : Bool
    equalNumericalValuesDoNotEstablishSymbolIdentity : Bool
    obstructionReplayDoesNotPaySourceFaithfulSolve : Bool

open THFDiscretizationBoundary public

canonicalTHFDiscretizationBoundary : THFDiscretizationBoundary
canonicalTHFDiscretizationBoundary =
  thf-discretization-boundary true true true true true
