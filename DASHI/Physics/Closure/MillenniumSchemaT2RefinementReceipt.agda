module DASHI.Physics.Closure.MillenniumSchemaT2RefinementReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema

------------------------------------------------------------------------
-- Millennium schema T2 refinement receipt.
--
-- This receipt refines only the T2 lift tier.  YM no longer has a single
-- undifferentiated T2 blocker: the p-adic lift is recorded as inhabited by
-- the Bruhat-Tits flat limit, while the archimedean H^3 -> R^3 lift stays
-- open.  NS keeps its single T2 blocker: large-data contraction in H^11/8.
-- The schema correspondence at T2 is therefore YM T2b <-> NS T2.  YM T2a
-- has no NS analogue.  No Clay promotion is made.

data MillenniumSchemaT2RefinementStatus : Set where
  t2SplitRecordedNoClayPromotion :
    MillenniumSchemaT2RefinementStatus

data YangMillsT2RefinedTier : Set where
  ymT2a :
    YangMillsT2RefinedTier

  ymT2b :
    YangMillsT2RefinedTier

pAdicLift :
  YangMillsT2RefinedTier
pAdicLift =
  ymT2a

archimedeanLift :
  YangMillsT2RefinedTier
archimedeanLift =
  ymT2b

data YangMillsT2RefinedStatus : Set where
  ymT2Inhabited :
    YangMillsT2RefinedStatus

  ymT2Open :
    YangMillsT2RefinedStatus

ymT2aStatus :
  YangMillsT2RefinedStatus
ymT2aStatus =
  ymT2Inhabited

ymT2bStatus :
  YangMillsT2RefinedStatus
ymT2bStatus =
  ymT2Open

data YangMillsT2aWitness : Set where
  bruhatTitsFlatLimit :
    YangMillsT2aWitness

data YangMillsT2bOpenObligation : Set where
  H3ToR3FlatLimit :
    YangMillsT2bOpenObligation

data NavierStokesT2RefinedTier : Set where
  nsT2 :
    NavierStokesT2RefinedTier

data NavierStokesT2RefinedStatus : Set where
  nsT2Open :
    NavierStokesT2RefinedStatus

nsT2Status :
  NavierStokesT2RefinedStatus
nsT2Status =
  nsT2Open

data NavierStokesT2OpenObligation : Set where
  largeDataContraction :
    NavierStokesT2OpenObligation

data T2SchemaCorrespondence : Set where
  ymT2bToNsT2 :
    T2SchemaCorrespondence

data NoNSAnalogueForYMT2a : Set where
  noAnalogue :
    NoNSAnalogueForYMT2a

canonicalYMT2RefinedTiers :
  List YangMillsT2RefinedTier
canonicalYMT2RefinedTiers =
  ymT2a
  ∷ ymT2b
  ∷ []

canonicalYMT2aWitnesses :
  List YangMillsT2aWitness
canonicalYMT2aWitnesses =
  bruhatTitsFlatLimit
  ∷ []

canonicalYMT2bOpenObligations :
  List YangMillsT2bOpenObligation
canonicalYMT2bOpenObligations =
  H3ToR3FlatLimit
  ∷ []

canonicalNST2OpenObligations :
  List NavierStokesT2OpenObligation
canonicalNST2OpenObligations =
  largeDataContraction
  ∷ []

data MillenniumSchemaT2RefinementPromotion : Set where

millenniumSchemaT2RefinementPromotionImpossibleHere :
  MillenniumSchemaT2RefinementPromotion →
  ⊥
millenniumSchemaT2RefinementPromotionImpossibleHere ()

t2RefinementStatement :
  String
t2RefinementStatement =
  "YM T2 splits into T2a pAdicLift inhabited by the Bruhat-Tits flat limit and T2b archimedeanLift open for H^3 -> R^3; NS T2 remains the open largeDataContraction tier."

t2CorrespondenceStatement :
  String
t2CorrespondenceStatement =
  "The schema isomorphism at T2 is refined to ymT2b <-> nsT2; ymT2a has no NS analogue."

record MillenniumSchemaT2RefinementReceipt : Setω where
  field
    status :
      MillenniumSchemaT2RefinementStatus

    baseSchema :
      Schema.MillenniumTowerSchemaReceipt

    baseSchemaIsCanonical :
      baseSchema ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    refinedSchemaTier :
      Schema.MillenniumTowerSchemaStage

    refinedSchemaTierIsT2 :
      refinedSchemaTier ≡ Schema.T2

    ymT2Tiers :
      List YangMillsT2RefinedTier

    ymT2TiersAreCanonical :
      ymT2Tiers ≡ canonicalYMT2RefinedTiers

    ymT2aTier :
      YangMillsT2RefinedTier

    ymT2aIsPAdicLift :
      ymT2aTier ≡ pAdicLift

    ymT2aStatusValue :
      YangMillsT2RefinedStatus

    ymT2aStatusIsInhabited :
      ymT2aStatusValue ≡ ymT2Inhabited

    ymT2aWitnesses :
      List YangMillsT2aWitness

    ymT2aWitnessesAreCanonical :
      ymT2aWitnesses ≡ canonicalYMT2aWitnesses

    ymT2bTier :
      YangMillsT2RefinedTier

    ymT2bIsArchimedeanLift :
      ymT2bTier ≡ archimedeanLift

    ymT2bStatusValue :
      YangMillsT2RefinedStatus

    ymT2bStatusIsOpen :
      ymT2bStatusValue ≡ ymT2Open

    ymT2bOpenObligations :
      List YangMillsT2bOpenObligation

    ymT2bOpenObligationsAreCanonical :
      ymT2bOpenObligations ≡ canonicalYMT2bOpenObligations

    nsT2Tier :
      NavierStokesT2RefinedTier

    nsT2StatusValue :
      NavierStokesT2RefinedStatus

    nsT2StatusIsOpen :
      nsT2StatusValue ≡ nsT2Open

    nsT2OpenObligations :
      List NavierStokesT2OpenObligation

    nsT2OpenObligationsAreCanonical :
      nsT2OpenObligations ≡ canonicalNST2OpenObligations

    schemaIsomorphismT2 :
      T2SchemaCorrespondence

    schemaIsomorphismT2IsYMT2bToNST2 :
      schemaIsomorphismT2 ≡ ymT2bToNsT2

    ymT2aNSAnalogue :
      NoNSAnalogueForYMT2a

    ymT2aNSAnalogueIsNone :
      ymT2aNSAnalogue ≡ noAnalogue

    pAdicLiftInhabited :
      Bool

    pAdicLiftInhabitedIsTrue :
      pAdicLiftInhabited ≡ true

    archimedeanLiftOpen :
      Bool

    archimedeanLiftOpenIsTrue :
      archimedeanLiftOpen ≡ true

    nsLargeDataContractionOpen :
      Bool

    nsLargeDataContractionOpenIsTrue :
      nsLargeDataContractionOpen ≡ true

    t2RefinementText :
      String

    t2RefinementTextIsCanonical :
      t2RefinementText ≡ t2RefinementStatement

    t2CorrespondenceText :
      String

    t2CorrespondenceTextIsCanonical :
      t2CorrespondenceText ≡ t2CorrespondenceStatement

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List MillenniumSchemaT2RefinementPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open MillenniumSchemaT2RefinementReceipt public

canonicalMillenniumSchemaT2RefinementReceipt :
  MillenniumSchemaT2RefinementReceipt
canonicalMillenniumSchemaT2RefinementReceipt =
  record
    { status =
        t2SplitRecordedNoClayPromotion
    ; baseSchema =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; baseSchemaIsCanonical =
        refl
    ; refinedSchemaTier =
        Schema.T2
    ; refinedSchemaTierIsT2 =
        refl
    ; ymT2Tiers =
        canonicalYMT2RefinedTiers
    ; ymT2TiersAreCanonical =
        refl
    ; ymT2aTier =
        pAdicLift
    ; ymT2aIsPAdicLift =
        refl
    ; ymT2aStatusValue =
        ymT2Inhabited
    ; ymT2aStatusIsInhabited =
        refl
    ; ymT2aWitnesses =
        canonicalYMT2aWitnesses
    ; ymT2aWitnessesAreCanonical =
        refl
    ; ymT2bTier =
        archimedeanLift
    ; ymT2bIsArchimedeanLift =
        refl
    ; ymT2bStatusValue =
        ymT2Open
    ; ymT2bStatusIsOpen =
        refl
    ; ymT2bOpenObligations =
        canonicalYMT2bOpenObligations
    ; ymT2bOpenObligationsAreCanonical =
        refl
    ; nsT2Tier =
        nsT2
    ; nsT2StatusValue =
        nsT2Open
    ; nsT2StatusIsOpen =
        refl
    ; nsT2OpenObligations =
        canonicalNST2OpenObligations
    ; nsT2OpenObligationsAreCanonical =
        refl
    ; schemaIsomorphismT2 =
        ymT2bToNsT2
    ; schemaIsomorphismT2IsYMT2bToNST2 =
        refl
    ; ymT2aNSAnalogue =
        noAnalogue
    ; ymT2aNSAnalogueIsNone =
        refl
    ; pAdicLiftInhabited =
        true
    ; pAdicLiftInhabitedIsTrue =
        refl
    ; archimedeanLiftOpen =
        true
    ; archimedeanLiftOpenIsTrue =
        refl
    ; nsLargeDataContractionOpen =
        true
    ; nsLargeDataContractionOpenIsTrue =
        refl
    ; t2RefinementText =
        t2RefinementStatement
    ; t2RefinementTextIsCanonical =
        refl
    ; t2CorrespondenceText =
        t2CorrespondenceStatement
    ; t2CorrespondenceTextIsCanonical =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "YM T2 is refined into T2a pAdicLift and T2b archimedeanLift"
        ∷ "YM T2a is inhabited by the Bruhat-Tits flat limit"
        ∷ "YM T2b remains open as the archimedean H^3 -> R^3 lift"
        ∷ "NS T2 remains the open largeDataContraction tier"
        ∷ "The T2 schema correspondence is ymT2b <-> nsT2"
        ∷ "YM T2a has no NS analogue"
        ∷ "No Clay promotion is made"
        ∷ []
    }
