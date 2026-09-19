module DASHI.Analysis.RiemannG2QuantitativeScaledTaperLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- QUANTITATIVE FIXED-TEMPLATE TAPER SCAFFOLD
--
-- Mathlib's historical ContDiffBump constructor gives qualitative support and
-- positivity, but its public API does not expose the derivative-mass scaling
-- needed by the current RH magnitude audit.
--
-- Companion Lean source therefore fixes one unit bump and rescales it explicitly:
--
--   psi_{c,R}(u)=psi((u-c)/R).
--
-- Source-written:
--
--   support in |u-c|<R,
--   psi'_{c,R}=R^{-1} psi'(...),
--   psi''_{c,R}=R^{-2} psi''(...),
--
--   M0(psi_{c,R}) = R M0*,
--   M1(psi_{c,R}) = M1*,
--   M2(psi_{c,R}) = R^{-1} M2*,
--
-- with factor-two bounds after symmetrisation.
--
-- A scaled-bump positive-weight integral theorem is also source-written, and the
-- two canonical windows now have a t-independent abstract mixing-ratio bound
-- once their pole-response upper/lower inequalities are instantiated.
--
-- The historical taper has not yet been replaced by this quantitative taper.
------------------------------------------------------------------------

record QuantitativeScaledTaperLeanReceipt : Set where
  constructor quantitative-scaled-taper-lean-receipt
  field
    repository : String
    branch : String
    bumpPath : String
    massPath : String
    symmetricMassPath : String
    positivityPath : String
    mixingPath : String
    bumpCommit : String
    massCommit : String
    symmetricMassCommit : String
    positivityCommit : String
    mixingCommit : String

open QuantitativeScaledTaperLeanReceipt public

currentQuantitativeScaledTaperLeanReceipt : QuantitativeScaledTaperLeanReceipt
currentQuantitativeScaledTaperLeanReceipt =
  quantitative-scaled-taper-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannQuantitativeScaledBump.lean"
    "Synthesis/RiemannQuantitativeScaledBumpMass.lean"
    "Synthesis/RiemannQuantitativeSymmetricBumpMass.lean"
    "Synthesis/RiemannQuantitativeScaledBumpPositivity.lean"
    "Synthesis/RiemannQuantitativeTaperMixingBound.lean"
    "1c937b85ff6a8a01611c5163e41928119b078372"
    "28eb1b4f9b4583065278e3de6508177fe13ea76c"
    "560d0470d2e16873e49a1b55f783307ab67ea159"
    "74d3136a420a889dee48c770791b245143582690"
    "770b3bda7a6932f31f13f8ac5db69ec082fac5bd"

record QuantitativeScaledTaperBoundary : Set where
  constructor quantitative-scaled-taper-boundary
  field
    fixedTemplateAffineScalingSourceWritten : Bool
    exactL1ScalingSourceWritten : Bool
    symmetricL1BoundsSourceWritten : Bool
    positiveWeightedIntegralSourceWritten : Bool
    abstractUniformMixingRatioSourceWritten : Bool

    quantitativeCanonicalTaperConstructed : Bool
    quantitativeCanonicalTaperAttachedToFinalLane : Bool
    centeredOffEnvelopeAsymptoticScaleClosed : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    rhDerivedHere : Bool

open QuantitativeScaledTaperBoundary public

canonicalQuantitativeScaledTaperBoundary : QuantitativeScaledTaperBoundary
canonicalQuantitativeScaledTaperBoundary =
  quantitative-scaled-taper-boundary
    true
    true
    true
    true
    true

    false
    false
    false

    false
    false
    false
