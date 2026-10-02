{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.YanchukStableManifoldCrossingTargetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Physics.Dynamics.YanchukSelectedCrossSectionBracketExact as Bracket
import DASHI.Physics.Dynamics.YanchukSingularBasinSourceExact as Source

------------------------------------------------------------------------
-- Selected validation target for the Yanchuk normal-form stable manifold.
--
-- This module freezes the exact cross-section and source objects that a future
-- interval continuation checker must certify. It does not itself assert the
-- manifold crossing or basin separation theorem.
------------------------------------------------------------------------

record StableManifoldCrossingTarget : Set where
  constructor stableManifoldCrossingTarget
  field
    sourceDOI : String
    sourceRepository : String
    sourceModelFile : String
    sourceJacobianFile : String
    epsilonReading : String
    aReading : String
    bReading : String
    muCrossSectionReading : String
    crossingBracket : Bracket.AdjacentScaledBracket
    crossingBracketCanonical :
      crossingBracket ≡ Bracket.selectedBracket

    stableSaddleExistenceCertified : Bool
    stableEigenDirectionCertified : Bool
    manifoldContinuationCertified : Bool
    crossSectionTransversalityCertified : Bool
    twoSidedBasinSeparationCertified : Bool
    validatedCrossingPromotionComplete : Bool

open StableManifoldCrossingTarget public

canonicalStableManifoldCrossingTarget :
  StableManifoldCrossingTarget
canonicalStableManifoldCrossingTarget =
  stableManifoldCrossingTarget
    "10.1103/jtkh-9lz5"
    "https://github.com/hassanalkhayuon/Singular_Funnels"
    "Normal_forms/Normal_form_figure.m"
    "Normal_forms/Normal_form_figure.m::Jacobian_NF"
    "epsilon = 0.1"
    "a = -1"
    "b = 2.3"
    "mu = 3.9"
    Bracket.selectedBracket
    refl
    false
    false
    false
    false
    false
    false

record StableManifoldCrossingPromotionObligations : Set where
  constructor stableManifoldCrossingPromotionObligations
  field
    certifySaddleAndStableDirection : Bool
    certifyBackwardStableManifoldTube : Bool
    certifyCrossSectionTransversality : Bool
    certifyBracketContainsUniqueCrossing : Bool
    certifyNegativeSideLowerBasin : Bool
    certifyPositiveSideUpperBasin : Bool

open StableManifoldCrossingPromotionObligations public

canonicalStableManifoldCrossingPromotionObligations :
  StableManifoldCrossingPromotionObligations
canonicalStableManifoldCrossingPromotionObligations =
  stableManifoldCrossingPromotionObligations
    false false false false false false

record YanchukStableManifoldValidationBoundary : Set where
  constructor yanchukStableManifoldValidationBoundary
  field
    sourceJacobianSymbolicallyOwned : Bool
    sourceJacobianSymbolicallyOwnedIsTrue :
      sourceJacobianSymbolicallyOwned ≡ true
    exactCrossSectionBracketOwned : Bool
    exactCrossSectionBracketOwnedIsTrue :
      exactCrossSectionBracketOwned ≡ true
    sourceStableDirectionNumericallyReproduced : Bool
    sourceStableDirectionNumericallyReproducedIsFalse :
      sourceStableDirectionNumericallyReproduced ≡ false
    intervalStableManifoldTubeCertified : Bool
    intervalStableManifoldTubeCertifiedIsFalse :
      intervalStableManifoldTubeCertified ≡ false
    basinSeparationTheoremCertified : Bool
    basinSeparationTheoremCertifiedIsFalse :
      basinSeparationTheoremCertified ≡ false

canonicalYanchukStableManifoldValidationBoundary :
  YanchukStableManifoldValidationBoundary
canonicalYanchukStableManifoldValidationBoundary =
  yanchukStableManifoldValidationBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
