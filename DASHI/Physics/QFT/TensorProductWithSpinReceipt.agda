module DASHI.Physics.QFT.TensorProductWithSpinReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.DiracSpinSectorReceipt as Dirac
import DASHI.Physics.QFT.SpinStatisticsConnectionReceipt as SpinStats

------------------------------------------------------------------------
-- Conditional tensor product with a Dirac spin sector.
--
-- This receipt supplies the missing import surface for the DHR non-abelian
-- route.  It records the conditional construction
--
--   rho_q_i = rho_p_i tensor rho_spin
--   C_phys  = C_CM boxtimes C_spin
--
-- and keeps the carrier derivation, full DHR construction, and exact
-- Standard-Model reconstruction false.  The fermionic conclusion is
-- conditional on the separately recorded Dirac spin-sector candidate.

data TensorProductWithSpinStatus : Set where
  conditionalPhysicalQuarkSectorCandidate :
    TensorProductWithSpinStatus

data PrimeLaneSectorLabel : Set where
  rho-p2 :
    PrimeLaneSectorLabel

  rho-p3 :
    PrimeLaneSectorLabel

  rho-p5 :
    PrimeLaneSectorLabel

canonicalPrimeLaneSectorLabels :
  List PrimeLaneSectorLabel
canonicalPrimeLaneSectorLabels =
  rho-p2
  ∷ rho-p3
  ∷ rho-p5
  ∷ []

data TensorProductWithSpinBlocker : Set where
  missingCarrierDerivationOfSpinSector :
    TensorProductWithSpinBlocker

  missingDHRLocalisationForTensorProductSectors :
    TensorProductWithSpinBlocker

  missingPhysicalIntertwinerConstruction :
    TensorProductWithSpinBlocker

  missingExactStandardModelGaugeReconstruction :
    TensorProductWithSpinBlocker

canonicalTensorProductWithSpinBlockers :
  List TensorProductWithSpinBlocker
canonicalTensorProductWithSpinBlockers =
  missingCarrierDerivationOfSpinSector
  ∷ missingDHRLocalisationForTensorProductSectors
  ∷ missingPhysicalIntertwinerConstruction
  ∷ missingExactStandardModelGaugeReconstruction
  ∷ []

data TensorProductWithSpinPromotion : Set where

tensorProductWithSpinPromotionImpossibleHere :
  TensorProductWithSpinPromotion →
  ⊥
tensorProductWithSpinPromotionImpossibleHere ()

physicalQuarkSectorFormulaLabel : String
physicalQuarkSectorFormulaLabel =
  "rho_q_i = rho_p_i tensor rho_spin"

physicalCategoryLabel : String
physicalCategoryLabel =
  "C_phys = C_CM boxtimes C_spin"

fermionicStatisticsConditionalLabel : String
fermionicStatisticsConditionalLabel =
  "epsilon(rho_q_i,rho_q_i)=+1 tensor -1 = -1, conditional on rho_spin"

rhoQP2TensorSpinLabel : String
rhoQP2TensorSpinLabel =
  "rho_q_p2 = rho_p2 tensor rho_spin"

rhoQP3TensorSpinLabel : String
rhoQP3TensorSpinLabel =
  "rho_q_p3 = rho_p3 tensor rho_spin"

rhoQP5TensorSpinLabel : String
rhoQP5TensorSpinLabel =
  "rho_q_p5 = rho_p5 tensor rho_spin"

record TensorProductWithSpinReceipt : Setω where
  field
    status :
      TensorProductWithSpinStatus

    diracSpinSectorReceipt :
      Dirac.DiracSpinSectorReceipt

    diracSpinSectorReceiptIsCanonical :
      Bool

    diracSpinSectorReceiptIsCanonicalIsTrue :
      diracSpinSectorReceiptIsCanonical ≡ true

    spinStatisticsConnectionReceipt :
      SpinStats.SpinStatisticsConnectionReceipt

    spinStatisticsConnectionReceiptIsCanonical :
      Bool

    spinStatisticsConnectionReceiptIsCanonicalIsTrue :
      spinStatisticsConnectionReceiptIsCanonical ≡ true

    primeLaneSectors :
      List PrimeLaneSectorLabel

    primeLaneSectorsAreCanonical :
      primeLaneSectors ≡ canonicalPrimeLaneSectorLabels

    p2PhysicalQuarkSector :
      String

    p2PhysicalQuarkSectorIsTensorWithSpin :
      p2PhysicalQuarkSector ≡ rhoQP2TensorSpinLabel

    p3PhysicalQuarkSector :
      String

    p3PhysicalQuarkSectorIsTensorWithSpin :
      p3PhysicalQuarkSector ≡ rhoQP3TensorSpinLabel

    p5PhysicalQuarkSector :
      String

    p5PhysicalQuarkSectorIsTensorWithSpin :
      p5PhysicalQuarkSector ≡ rhoQP5TensorSpinLabel

    quarkSectorFormula :
      String

    quarkSectorFormulaIsCanonical :
      quarkSectorFormula ≡ physicalQuarkSectorFormulaLabel

    physicalCategory :
      String

    physicalCategoryIsCanonical :
      physicalCategory ≡ physicalCategoryLabel

    fermionicStatisticsConditional :
      String

    fermionicStatisticsConditionalIsCanonical :
      fermionicStatisticsConditional ≡ fermionicStatisticsConditionalLabel

    spinSectorFermionicByConstruction :
      Bool

    spinSectorFermionicByConstructionIsTrue :
      spinSectorFermionicByConstruction ≡ true

    physicalQuarkSectorsFermionic :
      Bool

    physicalQuarkSectorsFermionicIsTrue :
      physicalQuarkSectorsFermionic ≡ true

    physicalQuarkSectorsFermionicConditional :
      Bool

    physicalQuarkSectorsFermionicConditionalIsTrue :
      physicalQuarkSectorsFermionicConditional ≡ true

    physicalQuarkSectorsFermionicConditionalOnDiracSpinCandidate :
      physicalQuarkSectorsFermionic
      ≡
      Dirac.fermionicByConstruction diracSpinSectorReceipt

    spinSectorDerivedFromCarrier :
      Bool

    spinSectorDerivedFromCarrierIsFalse :
      spinSectorDerivedFromCarrier ≡ false

    fullDHRLocalisedTensorProductConstructed :
      Bool

    fullDHRLocalisedTensorProductConstructedIsFalse :
      fullDHRLocalisedTensorProductConstructed ≡ false

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    promotionFlags :
      List TensorProductWithSpinPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List TensorProductWithSpinBlocker

    blockersAreCanonical :
      blockers ≡ canonicalTensorProductWithSpinBlockers

    receiptBoundary :
      List String

open TensorProductWithSpinReceipt public

canonicalTensorProductWithSpinReceipt :
  TensorProductWithSpinReceipt
canonicalTensorProductWithSpinReceipt =
  record
    { status =
        conditionalPhysicalQuarkSectorCandidate
    ; diracSpinSectorReceipt =
        Dirac.canonicalDiracSpinSectorReceipt
    ; diracSpinSectorReceiptIsCanonical =
        true
    ; diracSpinSectorReceiptIsCanonicalIsTrue =
        refl
    ; spinStatisticsConnectionReceipt =
        SpinStats.canonicalSpinStatisticsConnectionReceipt
    ; spinStatisticsConnectionReceiptIsCanonical =
        true
    ; spinStatisticsConnectionReceiptIsCanonicalIsTrue =
        refl
    ; primeLaneSectors =
        canonicalPrimeLaneSectorLabels
    ; primeLaneSectorsAreCanonical =
        refl
    ; p2PhysicalQuarkSector =
        rhoQP2TensorSpinLabel
    ; p2PhysicalQuarkSectorIsTensorWithSpin =
        refl
    ; p3PhysicalQuarkSector =
        rhoQP3TensorSpinLabel
    ; p3PhysicalQuarkSectorIsTensorWithSpin =
        refl
    ; p5PhysicalQuarkSector =
        rhoQP5TensorSpinLabel
    ; p5PhysicalQuarkSectorIsTensorWithSpin =
        refl
    ; quarkSectorFormula =
        physicalQuarkSectorFormulaLabel
    ; quarkSectorFormulaIsCanonical =
        refl
    ; physicalCategory =
        physicalCategoryLabel
    ; physicalCategoryIsCanonical =
        refl
    ; fermionicStatisticsConditional =
        fermionicStatisticsConditionalLabel
    ; fermionicStatisticsConditionalIsCanonical =
        refl
    ; spinSectorFermionicByConstruction =
        Dirac.fermionicByConstruction Dirac.canonicalDiracSpinSectorReceipt
    ; spinSectorFermionicByConstructionIsTrue =
        Dirac.diracSpinSectorIsFermionicByConstruction
    ; physicalQuarkSectorsFermionic =
        true
    ; physicalQuarkSectorsFermionicIsTrue =
        refl
    ; physicalQuarkSectorsFermionicConditional =
        true
    ; physicalQuarkSectorsFermionicConditionalIsTrue =
        refl
    ; physicalQuarkSectorsFermionicConditionalOnDiracSpinCandidate =
        refl
    ; spinSectorDerivedFromCarrier =
        Dirac.derivationFromCarrier Dirac.canonicalDiracSpinSectorReceipt
    ; spinSectorDerivedFromCarrierIsFalse =
        Dirac.diracSpinSectorNotDerivedFromCarrierHere
    ; fullDHRLocalisedTensorProductConstructed =
        false
    ; fullDHRLocalisedTensorProductConstructedIsFalse =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; blockers =
        canonicalTensorProductWithSpinBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "Physical quark sectors are recorded as rho_p_i tensor rho_spin candidates"
        ∷ "The recorded sectors are rho_q_p2, rho_q_p3, and rho_q_p5"
        ∷ "Fermionic statistics is true only conditional on the separate rho_spin candidate receipt"
        ∷ "The spin sector is not yet derived from carrier data"
        ∷ "No exact G_DHR = G_SM or full DHR tensor-product promotion is claimed"
        ∷ []
    }

tensorProductWithSpinNoExactSMPromotion :
  exactGDHREqualsGSM canonicalTensorProductWithSpinReceipt ≡ false
tensorProductWithSpinNoExactSMPromotion =
  refl
