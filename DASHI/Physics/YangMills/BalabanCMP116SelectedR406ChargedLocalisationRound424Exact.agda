{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedR406ChargedLocalisationRound424Exact where

------------------------------------------------------------------------
-- ROUND424 / INSTANTIATE EXISTING CMP116 CHARGED LOCALISATION SUM ON R406
--
-- This is NOT a new residual-summability ABI.
--
-- BalabanMarkedPolarisationResummation already contains the source-shaped
-- CMP116 theorem
--
--   sum chargedMajorant (localisations scale x y) <= nearEnvelope.
--
-- R421 consumes instead
--
--   sum (expNeg o residualCharge) R406.localizedDomains <= residualEnvelope.
--
-- The mature source theorem hides its own Localisation carrier whereas R406
-- has its selected Domain.  Therefore the least-privilege application theorem
-- supplies:
--
--   * a map from each selected R406 domain to the source localisation carrier;
--   * exact list identity: source localisations = map sourceLocalization R406 list;
--   * pointwise identity: selected residual exponential = source chargedMajorant;
--   * exact envelope identity.
--
-- Finite transport across map/list/function equality is proved below.  The
-- actual inequality is chargedLocalisationSummability from the existing
-- marked-resummation owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Nat.Base using (ℕ)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanCMP116ExternalMarkResidualSummationRound423Exact as R423

------------------------------------------------------------------------
-- Generic finite transport, deliberately proved here rather than assumed.
------------------------------------------------------------------------

sumMapExact :
  ∀ {A B : Set}
    (f : A → B)
    (weight : B → ℝ)
    (xs : List A) →
  Resum.sumℝ weight (map f xs)
  ≡
  Resum.sumℝ (λ x → weight (f x)) xs
sumMapExact f weight [] = refl
sumMapExact f weight (x ∷ xs)
  rewrite sumMapExact f weight xs = refl

sumPointwiseExact :
  ∀ {A : Set}
    (left right : A → ℝ)
    (xs : List A) →
  (∀ x → left x ≡ right x) →
  Resum.sumℝ left xs ≡ Resum.sumℝ right xs
sumPointwiseExact left right [] pointwise = refl
sumPointwiseExact left right (x ∷ xs) pointwise
  rewrite pointwise x
        | sumPointwiseExact left right xs pointwise = refl

------------------------------------------------------------------------
-- Literal selected attachment to the existing source theorem.
------------------------------------------------------------------------

record SelectedR406ChargedLocalisationAttachment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    {SourceDomain Background History : Set}
    (resummation :
      Resum.MarkedLocalisationResummationData SourceDomain Background History)
    (exponential : R423.NegativeExponentialFactorization)
    (residualCharge : R406.Domain application → ℝ)
    (residualEnvelope : ℝ) : Set₂ where
  field
    scale : ℕ
    beforeDomain afterDomain : SourceDomain
    background : Background
    history : History
    leftCube rightCube : Resum.Cube resummation

    sourceLocalization :
      R406.Domain application → Resum.Localisation resummation

    sourceLocalisationsAreSelectedR406Map :
      Resum.localisations resummation scale leftCube rightCube
      ≡
      map sourceLocalization (R406.localizedDomains application)

    residualExponentialIsSourceChargedMajorant :
      ∀ domain →
      R423.negativeExp exponential (residualCharge domain)
      ≡
      Resum.chargedMajorant resummation
        scale beforeDomain afterDomain background history
        (sourceLocalization domain) leftCube rightCube

    residualEnvelopeIsSourceNearEnvelope :
      residualEnvelope
      ≡
      Resum.nearEnvelope resummation
        scale beforeDomain afterDomain background history
        leftCube rightCube

open SelectedR406ChargedLocalisationAttachment public

selectedResidualSummabilityFromExistingCMP116 :
  ∀ {Measure TestObservable dataSet extension base application}
    {SourceDomain Background History}
    {resummation :
      Resum.MarkedLocalisationResummationData SourceDomain Background History}
    {exponential : R423.NegativeExponentialFactorization}
    {residualCharge : R406.Domain application → ℝ}
    {residualEnvelope : ℝ}
    (attachment :
      SelectedR406ChargedLocalisationAttachment
        {dataSet = dataSet} {extension = extension} {base = base}
        application resummation exponential residualCharge residualEnvelope) →
  Resum.sumℝ
    (λ domain → R423.negativeExp exponential (residualCharge domain))
    (R406.localizedDomains application)
  ≤ℝ residualEnvelope
selectedResidualSummabilityFromExistingCMP116
    {application = application}
    {resummation = resummation}
    {exponential = exponential}
    {residualCharge = residualCharge}
    {residualEnvelope = residualEnvelope}
    attachment =
  let
    sourceWeight : Resum.Localisation resummation → ℝ
    sourceWeight localization =
      Resum.chargedMajorant resummation
        (scale attachment)
        (beforeDomain attachment)
        (afterDomain attachment)
        (background attachment)
        (history attachment)
        localization
        (leftCube attachment)
        (rightCube attachment)

    selectedWeight : R406.Domain application → ℝ
    selectedWeight domain =
      R423.negativeExp exponential (residualCharge domain)

    sourceBound :
      Resum.sumℝ sourceWeight
        (Resum.localisations resummation
          (scale attachment)
          (leftCube attachment)
          (rightCube attachment))
      ≤ℝ
      Resum.nearEnvelope resummation
        (scale attachment)
        (beforeDomain attachment)
        (afterDomain attachment)
        (background attachment)
        (history attachment)
        (leftCube attachment)
        (rightCube attachment)
    sourceBound =
      Resum.chargedLocalisationSummability resummation
        (scale attachment)
        (beforeDomain attachment)
        (afterDomain attachment)
        (background attachment)
        (history attachment)
        (leftCube attachment)
        (rightCube attachment)

    mappedBound :
      Resum.sumℝ sourceWeight
        (map (sourceLocalization attachment)
          (R406.localizedDomains application))
      ≤ℝ
      Resum.nearEnvelope resummation
        (scale attachment)
        (beforeDomain attachment)
        (afterDomain attachment)
        (background attachment)
        (history attachment)
        (leftCube attachment)
        (rightCube attachment)
    mappedBound =
      subst
        (λ localisations →
          Resum.sumℝ sourceWeight localisations
          ≤ℝ
          Resum.nearEnvelope resummation
            (scale attachment)
            (beforeDomain attachment)
            (afterDomain attachment)
            (background attachment)
            (history attachment)
            (leftCube attachment)
            (rightCube attachment))
        (sourceLocalisationsAreSelectedR406Map attachment)
        sourceBound

    composedBound :
      Resum.sumℝ
        (λ domain → sourceWeight (sourceLocalization attachment domain))
        (R406.localizedDomains application)
      ≤ℝ
      Resum.nearEnvelope resummation
        (scale attachment)
        (beforeDomain attachment)
        (afterDomain attachment)
        (background attachment)
        (history attachment)
        (leftCube attachment)
        (rightCube attachment)
    composedBound =
      subst
        (λ lower →
          lower
          ≤ℝ
          Resum.nearEnvelope resummation
            (scale attachment)
            (beforeDomain attachment)
            (afterDomain attachment)
            (background attachment)
            (history attachment)
            (leftCube attachment)
            (rightCube attachment))
        (sumMapExact
          (sourceLocalization attachment)
          sourceWeight
          (R406.localizedDomains application))
        mappedBound

    selectedBound :
      Resum.sumℝ selectedWeight (R406.localizedDomains application)
      ≤ℝ
      Resum.nearEnvelope resummation
        (scale attachment)
        (beforeDomain attachment)
        (afterDomain attachment)
        (background attachment)
        (history attachment)
        (leftCube attachment)
        (rightCube attachment)
    selectedBound =
      subst
        (λ lower →
          lower
          ≤ℝ
          Resum.nearEnvelope resummation
            (scale attachment)
            (beforeDomain attachment)
            (afterDomain attachment)
            (background attachment)
            (history attachment)
            (leftCube attachment)
            (rightCube attachment))
        (sym
          (sumPointwiseExact
            selectedWeight
            (λ domain → sourceWeight (sourceLocalization attachment domain))
            (R406.localizedDomains application)
            (residualExponentialIsSourceChargedMajorant attachment)))
        composedBound
  in
  subst
    (λ upper →
      Resum.sumℝ selectedWeight (R406.localizedDomains application)
      ≤ℝ upper)
    (sym (residualEnvelopeIsSourceNearEnvelope attachment))
    selectedBound

round424FiniteCarrierTransportLevel : ProofLevel
round424FiniteCarrierTransportLevel = machineChecked

round424CMP116SummabilityTheoremLevel : ProofLevel
round424CMP116SummabilityTheoremLevel = standardImported

round424SelectedLocalisationFamilyAttachmentLevel : ProofLevel
round424SelectedLocalisationFamilyAttachmentLevel = conditional

round424SelectedChargedMajorantAttachmentLevel : ProofLevel
round424SelectedChargedMajorantAttachmentLevel = conditional

round424SelectedNearEnvelopeAttachmentLevel : ProofLevel
round424SelectedNearEnvelopeAttachmentLevel = conditional

round424FreshResidualSummabilityTheoremRequired : Bool
round424FreshResidualSummabilityTheoremRequired = false
