{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedExternalNestedFoldRound622Exact where

------------------------------------------------------------------------
-- ROUND622 / CANONICAL ORBIT-RESOLVED EXTERNAL R573 FOLD
--
-- R620 rewrites one external R573 nested cell once an R619 orbit-resolved
-- selection is supplied.  R621 makes that selection executable from literal
-- Fourier-mode equality, and R616 transports membership in a fixed output fibre
-- to the incidence's own k-fibre.
--
-- Therefore the complete external nested fold on one physical output fibre can
-- be rewritten onto a canonical orbit-resolved finite fold with no:
--
--   * legacy R112 witness family,
--   * global nonfixedness assumption,
--   * exceptional-locus exclusion, or
--   * user-supplied fixed/nonfixed choices.
--
-- Fixed-orbit multiplicity corrections remain inside the R618/R619 vectors.
-- No estimate, norm, absolute value, or cancellation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any as Any
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNThreeLegResidualMembershipCompilerRound616Exact as R616
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeOrbitResolvedRound619Exact as R619
import DASHI.Physics.Closure.NSTriadKNR573OrbitResolvedExternalNestedRound620Exact as R620
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedSelectionRound621Exact as R621

module CanonicalExternalNested
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Split =
    R613.NestedNetworkSplit W S L H system velocityTransverse
  module Total =
    R620.OrbitResolvedExternalNested W S L H system velocityTransverse

  fibre : Z3.FourierMode → List Physical.PhysicalTriadIncidence
  fibre output =
    Output.physicalOutputFiber (Audit.cutoff system) output

  canonicalSelectionFromFibre :
    (output : Z3.FourierMode) →
    (tau : Physical.PhysicalTriadIncidence) →
    tau ∈ fibre output →
    R619.ThreeLegOrbitResolvedSelection system tau
  canonicalSelectionFromFibre output tau member =
    R621.canonicalThreeLegOrbitResolvedSelection
      system tau
      (R616.canonicalFibreMemberToOwnFibre
        system output tau member)

  canonicalExternalNestedCell :
    (output : Z3.FourierMode) →
    (tau : Physical.PhysicalTriadIncidence) →
    tau ∈ fibre output →
    C3.Complex3 F
  canonicalExternalNestedCell output tau member =
    Total.externalResolvedNestedWeightedCompanionCell
      tau
      (canonicalSelectionFromFibre output tau member)

  externalNestedCellIsCanonical :
    (output : Z3.FourierMode) →
    (tau : Physical.PhysicalTriadIncidence) →
    (member : tau ∈ fibre output) →
    Split.externalNestedWeightedCompanionCell tau
    ≡ canonicalExternalNestedCell output tau member
  externalNestedCellIsCanonical output tau member =
    Total.externalNestedWeightedCompanionIsOrbitResolved
      tau
      (canonicalSelectionFromFibre output tau member)

  canonicalExternalNestedFoldAux :
    (output : Z3.FourierMode) →
    (items : List Physical.PhysicalTriadIncidence) →
    (∀ {tau} → tau ∈ items → tau ∈ fibre output) →
    C3.Complex3 F
  canonicalExternalNestedFoldAux output [] include =
    C3.complex3Zero F
  canonicalExternalNestedFoldAux output (tau ∷ rest) include =
    C3.complex3Add
      (canonicalExternalNestedCell output tau
        (include (Any.here refl)))
      (canonicalExternalNestedFoldAux output rest
        (λ member → include (Any.there member)))

  externalNestedFoldAuxIsCanonical :
    (output : Z3.FourierMode) →
    (items : List Physical.PhysicalTriadIncidence) →
    (include : ∀ {tau} → tau ∈ items → tau ∈ fibre output) →
    R224.foldVector Split.externalNestedWeightedCompanionCell items
    ≡ canonicalExternalNestedFoldAux output items include
  externalNestedFoldAuxIsCanonical output [] include = refl
  externalNestedFoldAuxIsCanonical output (tau ∷ rest) include =
    cong₂ C3.complex3Add
      (externalNestedCellIsCanonical output tau
        (include (Any.here refl)))
      (externalNestedFoldAuxIsCanonical output rest
        (λ member → include (Any.there member)))

  canonicalExternalNestedFold :
    Z3.FourierMode → C3.Complex3 F
  canonicalExternalNestedFold output =
    canonicalExternalNestedFoldAux output (fibre output) (λ member → member)

  fixedOutputExternalNestedFoldIsCanonical :
    (output : Z3.FourierMode) →
    R224.foldVector Split.externalNestedWeightedCompanionCell (fibre output)
    ≡ canonicalExternalNestedFold output
  fixedOutputExternalNestedFoldIsCanonical output =
    externalNestedFoldAuxIsCanonical
      output (fibre output) (λ member → member)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round622CanonicalOrbitResolvedExternalNestedFoldConstructed : Bool
round622CanonicalOrbitResolvedExternalNestedFoldConstructed = true

round622FixedOutputExternalR573FoldSameObjectWeldClosed : Bool
round622FixedOutputExternalR573FoldSameObjectWeldClosed = true

round622RequiresUserSuppliedOrbitCases : Bool
round622RequiresUserSuppliedOrbitCases = false

round622RequiresLegacyR112WitnessFamily : Bool
round622RequiresLegacyR112WitnessFamily = false

round622FixedOrbitCorrectionPreserved : Bool
round622FixedOrbitCorrectionPreserved = true

round622IntroducesEstimate : Bool
round622IntroducesEstimate = false

round622ExternalAnalyticPaymentClosed : Bool
round622ExternalAnalyticPaymentClosed = false

round622CanonicalOrbitResolvedExternalNestedFoldConstructedIsTrue :
  round622CanonicalOrbitResolvedExternalNestedFoldConstructed ≡ true
round622CanonicalOrbitResolvedExternalNestedFoldConstructedIsTrue = refl

round622FixedOutputExternalR573FoldSameObjectWeldClosedIsTrue :
  round622FixedOutputExternalR573FoldSameObjectWeldClosed ≡ true
round622FixedOutputExternalR573FoldSameObjectWeldClosedIsTrue = refl

round622RequiresUserSuppliedOrbitCasesIsFalse :
  round622RequiresUserSuppliedOrbitCases ≡ false
round622RequiresUserSuppliedOrbitCasesIsFalse = refl

round622RequiresLegacyR112WitnessFamilyIsFalse :
  round622RequiresLegacyR112WitnessFamily ≡ false
round622RequiresLegacyR112WitnessFamilyIsFalse = refl

round622FixedOrbitCorrectionPreservedIsTrue :
  round622FixedOrbitCorrectionPreserved ≡ true
round622FixedOrbitCorrectionPreservedIsTrue = refl

round622IntroducesEstimateIsFalse :
  round622IntroducesEstimate ≡ false
round622IntroducesEstimateIsFalse = refl

round622ExternalAnalyticPaymentClosedIsFalse :
  round622ExternalAnalyticPaymentClosed ≡ false
round622ExternalAnalyticPaymentClosedIsFalse = refl
