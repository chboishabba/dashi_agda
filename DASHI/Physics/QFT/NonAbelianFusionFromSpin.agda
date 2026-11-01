module DASHI.Physics.QFT.NonAbelianFusionFromSpin where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.FiniteDHRAbelianReconstructionReceipt as Abelian
import DASHI.Physics.QFT.TensorProductWithSpinReceipt as SpinTensor

------------------------------------------------------------------------
-- Conditional non-abelian fusion from a spin sector.
--
-- This receipt records a narrow conditional upgrade.  If the spin sector is
-- identified with Rep(SU2), then the Clebsch-Gordan tensor rule for the
-- fundamental spin representation supplies non-abelian fusion inside
-- C_CM boxtimes C_spin.  The finite DHR candidate becomes
-- SU(2) x (Z/4 x Z/6 x Z/2).
--
-- This does not identify G_DHR with the Standard Model gauge group and does
-- not close the SU(3) colour sector.

data SpinSectorEquivalenceCondition : Set where
  spinSectorEquivalentToRepSU2 :
    SpinSectorEquivalenceCondition

spinSectorConditionLabel : String
spinSectorConditionLabel =
  "C_spin ~ Rep(SU2)"

data SpinIrrep : Set where
  spin-zero :
    SpinIrrep

  spin-half :
    SpinIrrep

  spin-one :
    SpinIrrep

spinIrrepDimension :
  SpinIrrep →
  Nat
spinIrrepDimension spin-zero =
  1
spinIrrepDimension spin-half =
  2
spinIrrepDimension spin-one =
  3

clebschGordanFundamentalRuleLabel : String
clebschGordanFundamentalRuleLabel =
  "spin-1/2 tensor spin-1/2 decomposes as spin-0 plus spin-1"

clebschGordanFundamentalDecomposition :
  List SpinIrrep
clebschGordanFundamentalDecomposition =
  spin-zero
  ∷ spin-one
  ∷ []

clebschGordanFundamentalSummandCount : Nat
clebschGordanFundamentalSummandCount =
  2

cmBoxtimesSpinCategoryLabel : String
cmBoxtimesSpinCategoryLabel =
  "C_CM boxtimes C_spin"

gDHRFiniteNonAbelianCandidateLabel : String
gDHRFiniteNonAbelianCandidateLabel =
  "SU(2) x (Z/4 x Z/6 x Z/2)"

data NonAbelianFusionFromSpinBlocker : Set where
  blockedByConditionalSpinSectorEquivalence :
    NonAbelianFusionFromSpinBlocker

  blockedByMissingFullArbitraryDHRClosure :
    NonAbelianFusionFromSpinBlocker

  blockedByMissingExactGDHRToGSMIdentification :
    NonAbelianFusionFromSpinBlocker

  blockedByOpenSU3ColourSector :
    NonAbelianFusionFromSpinBlocker

canonicalNonAbelianFusionFromSpinBlockers :
  List NonAbelianFusionFromSpinBlocker
canonicalNonAbelianFusionFromSpinBlockers =
  blockedByConditionalSpinSectorEquivalence
  ∷ blockedByMissingFullArbitraryDHRClosure
  ∷ blockedByMissingExactGDHRToGSMIdentification
  ∷ blockedByOpenSU3ColourSector
  ∷ []

record NonAbelianFusionFromSpinSectorReceipt : Setω where
  field
    finiteAbelianReceipt :
      Abelian.FiniteDHRAbelianReconstructionReceipt

    conditionalGDHRSMPromotionReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    tensorProductWithSpinReceipt :
      SpinTensor.TensorProductWithSpinReceipt

    tensorProductWithSpinIsConditionalFermionic :
      SpinTensor.physicalQuarkSectorsFermionicConditional
        tensorProductWithSpinReceipt
      ≡
      true

    tensorProductWithSpinKeepsExactGSMFalse :
      SpinTensor.exactGDHREqualsGSM tensorProductWithSpinReceipt
      ≡
      false

    tensorProductCategory :
      String

    tensorProductCategoryIsCanonical :
      tensorProductCategory ≡ cmBoxtimesSpinCategoryLabel

    spinSectorEquivalenceCondition :
      SpinSectorEquivalenceCondition

    spinSectorEquivalenceConditionLabel :
      String

    spinSectorEquivalenceConditionLabelIsCanonical :
      spinSectorEquivalenceConditionLabel ≡ spinSectorConditionLabel

    conditionRecorded :
      Bool

    conditionRecordedIsTrue :
      conditionRecorded ≡ true

    fundamentalSpinIrrep :
      SpinIrrep

    fundamentalSpinIrrepIsSpinHalf :
      fundamentalSpinIrrep ≡ spin-half

    fundamentalSpinDimension :
      Nat

    fundamentalSpinDimensionIsTwo :
      fundamentalSpinDimension ≡ spinIrrepDimension spin-half

    clebschGordanRuleLabel :
      String

    clebschGordanRuleLabelIsCanonical :
      clebschGordanRuleLabel ≡ clebschGordanFundamentalRuleLabel

    clebschGordanDecomposition :
      List SpinIrrep

    clebschGordanDecompositionIsCanonical :
      clebschGordanDecomposition ≡ clebschGordanFundamentalDecomposition

    clebschGordanSummandCount :
      Nat

    clebschGordanSummandCountIsTwo :
      clebschGordanSummandCount ≡ clebschGordanFundamentalSummandCount

    clebschGordanRulesRecorded :
      Bool

    clebschGordanRulesRecordedIsTrue :
      clebschGordanRulesRecorded ≡ true

    nonAbelianFusionFromSpinSector :
      Bool

    nonAbelianFusionFromSpinSectorIsTrue :
      nonAbelianFusionFromSpinSector ≡ true

    gDHRFiniteNonAbelianCandidate :
      String

    gDHRFiniteNonAbelianCandidateIsCanonical :
      gDHRFiniteNonAbelianCandidate ≡ gDHRFiniteNonAbelianCandidateLabel

    finiteCandidateRecorded :
      Bool

    finiteCandidateRecordedIsTrue :
      finiteCandidateRecorded ≡ true

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    su3ColourGapOpen :
      Bool

    su3ColourGapOpenIsTrue :
      su3ColourGapOpen ≡ true

    fullDHRDRReconstructionConstructed :
      Bool

    fullDHRDRReconstructionConstructedIsFalse :
      fullDHRDRReconstructionConstructed ≡ false

    residualBlockers :
      List NonAbelianFusionFromSpinBlocker

    residualBlockersAreCanonical :
      residualBlockers ≡ canonicalNonAbelianFusionFromSpinBlockers

    receiptBoundary :
      List String

open NonAbelianFusionFromSpinSectorReceipt public

canonicalNonAbelianFusionFromSpinSectorReceipt :
  NonAbelianFusionFromSpinSectorReceipt
canonicalNonAbelianFusionFromSpinSectorReceipt =
  record
    { finiteAbelianReceipt =
        Abelian.canonicalFiniteDHRAbelianReconstructionReceipt
    ; conditionalGDHRSMPromotionReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; tensorProductWithSpinReceipt =
        SpinTensor.canonicalTensorProductWithSpinReceipt
    ; tensorProductWithSpinIsConditionalFermionic =
        SpinTensor.physicalQuarkSectorsFermionicConditionalIsTrue
          SpinTensor.canonicalTensorProductWithSpinReceipt
    ; tensorProductWithSpinKeepsExactGSMFalse =
        SpinTensor.exactGDHREqualsGSMIsFalse
          SpinTensor.canonicalTensorProductWithSpinReceipt
    ; tensorProductCategory =
        cmBoxtimesSpinCategoryLabel
    ; tensorProductCategoryIsCanonical =
        refl
    ; spinSectorEquivalenceCondition =
        spinSectorEquivalentToRepSU2
    ; spinSectorEquivalenceConditionLabel =
        spinSectorConditionLabel
    ; spinSectorEquivalenceConditionLabelIsCanonical =
        refl
    ; conditionRecorded =
        true
    ; conditionRecordedIsTrue =
        refl
    ; fundamentalSpinIrrep =
        spin-half
    ; fundamentalSpinIrrepIsSpinHalf =
        refl
    ; fundamentalSpinDimension =
        2
    ; fundamentalSpinDimensionIsTwo =
        refl
    ; clebschGordanRuleLabel =
        clebschGordanFundamentalRuleLabel
    ; clebschGordanRuleLabelIsCanonical =
        refl
    ; clebschGordanDecomposition =
        clebschGordanFundamentalDecomposition
    ; clebschGordanDecompositionIsCanonical =
        refl
    ; clebschGordanSummandCount =
        2
    ; clebschGordanSummandCountIsTwo =
        refl
    ; clebschGordanRulesRecorded =
        true
    ; clebschGordanRulesRecordedIsTrue =
        refl
    ; nonAbelianFusionFromSpinSector =
        true
    ; nonAbelianFusionFromSpinSectorIsTrue =
        refl
    ; gDHRFiniteNonAbelianCandidate =
        gDHRFiniteNonAbelianCandidateLabel
    ; gDHRFiniteNonAbelianCandidateIsCanonical =
        refl
    ; finiteCandidateRecorded =
        true
    ; finiteCandidateRecordedIsTrue =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; su3ColourGapOpen =
        true
    ; su3ColourGapOpenIsTrue =
        refl
    ; fullDHRDRReconstructionConstructed =
        false
    ; fullDHRDRReconstructionConstructedIsFalse =
        refl
    ; residualBlockers =
        canonicalNonAbelianFusionFromSpinBlockers
    ; residualBlockersAreCanonical =
        refl
    ; receiptBoundary =
        "Condition recorded: C_spin ~ Rep(SU2)"
        ∷ "Under that condition, the Clebsch-Gordan rule spin-1/2 tensor spin-1/2 = spin-0 plus spin-1 gives non-abelian fusion in C_CM boxtimes C_spin"
        ∷ "The finite non-abelian DHR candidate is SU(2) x (Z/4 x Z/6 x Z/2)"
        ∷ "Exact G_DHR ~= G_SM remains false, full DR reconstruction is not constructed here, and the SU3 colour gap remains open"
        ∷ []
    }

nonAbelianFusionFromSpinSectorConditionalTrue :
  nonAbelianFusionFromSpinSector
    canonicalNonAbelianFusionFromSpinSectorReceipt
  ≡
  true
nonAbelianFusionFromSpinSectorConditionalTrue =
  refl

gDHRFiniteNonAbelianCandidateIsSU2TimesFiniteCM :
  gDHRFiniteNonAbelianCandidate
    canonicalNonAbelianFusionFromSpinSectorReceipt
  ≡
  "SU(2) x (Z/4 x Z/6 x Z/2)"
gDHRFiniteNonAbelianCandidateIsSU2TimesFiniteCM =
  refl

nonAbelianFusionFromSpinKeepsExactGDHRGSMFalse :
  exactGDHREqualsGSM canonicalNonAbelianFusionFromSpinSectorReceipt
  ≡
  false
nonAbelianFusionFromSpinKeepsExactGDHRGSMFalse =
  refl

nonAbelianFusionFromSpinKeepsSU3ColourGapOpen :
  su3ColourGapOpen canonicalNonAbelianFusionFromSpinSectorReceipt
  ≡
  true
nonAbelianFusionFromSpinKeepsSU3ColourGapOpen =
  refl
