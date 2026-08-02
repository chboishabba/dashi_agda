module DASHI.Physics.Closure.NSTriadKNDAnconaCommutatorFallbackAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- Venue/year: Journal of Fourier Analysis and Applications 25 (2019), no. 3,
-- 1134--1146.
-- DOI: 10.1007/s00041-018-9612-8.
-- arXiv/DataCite DOI: 10.48550/arXiv.1709.01294.
-- Correction title: "Correction to: A Short Proof of Commutator Estimates".
-- Correction venue/year: Journal of Fourier Analysis and Applications 26
-- (2020), article 23.
-- Correction DOI: 10.1007/s00041-019-09724-7.
-- Uses: the pointwise hypersingular difference representation and fractional
-- square-function control for 0 < s < 2.
-- Relationship: retained as a lighter commutator fallback.  The 2020 Hardy-
-- space correction is mandatory when an exponent is at or below one.  This
-- source does not replace the direct high-high-to-low convolution theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data CommutatorRoute : Set where
  directShellConvolution dAnconaPointwiseFallback classicalKatoPonceFallback :
    CommutatorRoute

selectedPrimaryRoute : CommutatorRoute
selectedPrimaryRoute = directShellConvolution

secondaryFallbackRoute : CommutatorRoute
secondaryFallbackRoute = dAnconaPointwiseFallback

record DAnconaScopeReceipt : Set where
  constructor receipt
  field
    originalArticlePeerReviewed : Bool
    correctionRecorded : Bool
    pointwiseDifferenceFormulaAvailable : Bool
    validFractionalRangeZeroToTwo : Bool
    HardyReplacementRequiredAtLowP : Bool
    periodicGalerkinOrbitTheoremSupplied : Bool
    selectedAsPrimaryStage3Route : Bool

open DAnconaScopeReceipt public

dAnconaScopeReceipt : DAnconaScopeReceipt
dAnconaScopeReceipt = receipt true true true true true false false

dAnconaBibliographyAndCorrectionVerified : Bool
dAnconaBibliographyAndCorrectionVerified = true

dAnconaBibliographyAndCorrectionVerifiedIsTrue :
  dAnconaBibliographyAndCorrectionVerified ≡ true
dAnconaBibliographyAndCorrectionVerifiedIsTrue = refl

dAnconaRetainedAsFallback : Bool
dAnconaRetainedAsFallback = true

dAnconaRetainedAsFallbackIsTrue : dAnconaRetainedAsFallback ≡ true
dAnconaRetainedAsFallbackIsTrue = refl

dAnconaClosesFirstAdjointConvolution : Bool
dAnconaClosesFirstAdjointConvolution = false

dAnconaClosesFirstAdjointConvolutionIsFalse :
  dAnconaClosesFirstAdjointConvolution ≡ false
dAnconaClosesFirstAdjointConvolutionIsFalse = refl
