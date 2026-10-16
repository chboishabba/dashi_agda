module DASHI.Moonshine.Monster3BSuzukiProofRelevantOccurrenceHardeningExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT SUZUKI / MAIN / MN3B / MONSTER OCCURRENCE GATE
--
-- The historical Suzuki same-object owner deliberately records the exact
-- class-table coordinates needed by the GAP/CTblLib producer.  Its semantic
-- obligations, however, are fields whose *values are Set*: they name the
-- propositions to be paid, but do not contain proofs inhabiting them.
--
-- Keep that useful legacy/data surface unchanged and wrap it.  A successful
-- external GAP run may populate/check positions, labels, multiplicities and
-- full class-function comparisons; it is still an execution certificate, not
-- an Agda proof term.  Promotion inside Agda requires inhabitants of the exact
-- obligations below.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonster3BSuzukiMainQuotientSameObjectSnowballExact as Suzuki

------------------------------------------------------------------------
-- 1. Pair-family identity.
------------------------------------------------------------------------

record PaidSuzukiPairFamilyIdentity
    (family : Suzuki.SuzukiPairFamilyIdentity) : Set₁ where
  field
    sixSuzToOuterRestrictionEqualityWitness :
      Suzuki.sixSuzToOuterRestrictionEquality family

open PaidSuzukiPairFamilyIdentity public

------------------------------------------------------------------------
-- 2. Main-table product split.
------------------------------------------------------------------------

record PaidMainTableProductSplit
    (split : Suzuki.MainTableProductSplit) : Set₁ where
  field
    splitByFullCharacterDecompositionWitness :
      Suzuki.splitByFullCharacterDecomposition split

open PaidMainTableProductSplit public

------------------------------------------------------------------------
-- 3. Quotient descent.  The paid split is tied to the exact nested split
--    object carried by this descent receipt.
------------------------------------------------------------------------

record PaidQuotientDescentMatch
    (descent : Suzuki.QuotientDescentMatch) : Set₁ where
  field
    productSplitPaid :
      PaidMainTableProductSplit (Suzuki.productSplit descent)
    fullPullbackCharacterEqualityWitness :
      Suzuki.fullPullbackCharacterEquality descent
    pairedPhaseCentralTraceWitness :
      Suzuki.pairedPhaseCentralTrace descent

open PaidQuotientDescentMatch public

------------------------------------------------------------------------
-- 4. Actual restricted-Monster occurrence.
------------------------------------------------------------------------

record PaidRestrictedMonsterOccurrence
    (occurrence : Suzuki.RestrictedMonsterOccurrence) : Set₁ where
  field
    descentPaid :
      PaidQuotientDescentMatch (Suzuki.descent occurrence)
    multiplicityPositiveWitness :
      Suzuki.multiplicityPositive occurrence
    sameMN3BIrreducibleObjectWitness :
      Suzuki.sameMN3BIrreducibleObject occurrence

open PaidRestrictedMonsterOccurrence public

------------------------------------------------------------------------
-- 5. Whole pair-family same-object receipt.
------------------------------------------------------------------------

record PaidSuzukiMainQuotientSameObjectReceipt
    (receipt : Suzuki.SuzukiMainQuotientSameObjectReceipt) : Set₁ where
  field
    base1458MatchesBarracloughFusedExtensionWitness :
      Suzuki.base1458MatchesBarracloughFusedExtension receipt

    twelveFamilyPaid :
      PaidSuzukiPairFamilyIdentity (Suzuki.twelveFamily receipt)
    seventyEightFamilyPaid :
      PaidSuzukiPairFamilyIdentity (Suzuki.seventyEightFamily receipt)

    twelveMonsterOccurrencePaid :
      PaidRestrictedMonsterOccurrence (Suzuki.twelveMonsterOccurrence receipt)
    seventyEightMonsterOccurrencePaid :
      PaidRestrictedMonsterOccurrence (Suzuki.seventyEightMonsterOccurrence receipt)

    primaryMainToMN3BQuotientMapSameObjectWitness :
      Suzuki.primaryMainToMN3BQuotientMapSameObject receipt
    actualMonster196883RestrictionSameObjectWitness :
      Suzuki.actualMonster196883RestrictionSameObject receipt
    pairFamilyMonsterOccurrenceWitness :
      Suzuki.pairFamilyMonsterOccurrencePaid receipt

open PaidSuzukiMainQuotientSameObjectReceipt public

------------------------------------------------------------------------
-- 6. Individual selected-zeta orientation remains a strictly stronger object.
--    A paid pair-family receipt is necessary but does not choose a/b.
------------------------------------------------------------------------

record PaidIndividualZetaOrientationReceipt
    {sameObject : Suzuki.SuzukiMainQuotientSameObjectReceipt}
    (orientation : Suzuki.IndividualZetaOrientationReceipt sameObject)
    : Set₁ where
  field
    pairFamilySameObjectPaid :
      PaidSuzukiMainQuotientSameObjectReceipt sameObject
    selectedExtraspecialZetaCharacterWitness :
      Suzuki.selectedExtraspecialZetaCharacter orientation
    quotientKernelCompatibilityTwelveWitness :
      Suzuki.quotientKernelCompatibilityTwelve orientation
    quotientKernelCompatibilitySeventyEightWitness :
      Suzuki.quotientKernelCompatibilitySeventyEight orientation
    phaseResolvedFullCharacterMatchWitness :
      Suzuki.phaseResolvedFullCharacterMatch orientation

open PaidIndividualZetaOrientationReceipt public

------------------------------------------------------------------------
-- 7. Explicit execution/proof firewalls.
------------------------------------------------------------------------

data GapBooleanCreatesAgdaCharacterEquality : Set where
data GapPositionCreatesSameObjectIrreducible : Set where
data PairFamilyOccurrenceCreatesZetaOrientation : Set where
data PositiveMultiplicityCreatesSameObjectWitness : Set where

gapBooleanDoesNotCreateAgdaCharacterEquality :
  GapBooleanCreatesAgdaCharacterEquality → ⊥
gapBooleanDoesNotCreateAgdaCharacterEquality ()

gapPositionDoesNotCreateSameObjectIrreducible :
  GapPositionCreatesSameObjectIrreducible → ⊥
gapPositionDoesNotCreateSameObjectIrreducible ()

pairFamilyDoesNotCreateZetaOrientation :
  PairFamilyOccurrenceCreatesZetaOrientation → ⊥
pairFamilyDoesNotCreateZetaOrientation ()

positiveMultiplicityDoesNotCreateSameObjectWitness :
  PositiveMultiplicityCreatesSameObjectWitness → ⊥
positiveMultiplicityDoesNotCreateSameObjectWitness ()

------------------------------------------------------------------------
-- 8. Machine-readable boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    legacyPairRestrictionObligationProofRelevant : Bool
    legacyMainSplitObligationProofRelevant : Bool
    legacyQuotientDescentObligationProofRelevant : Bool
    legacyMonsterOccurrenceObligationProofRelevant : Bool
    legacyOrientationObligationProofRelevant : Bool
    paidPairFamilyWrapperAvailable : Bool
    paidMainSplitWrapperAvailable : Bool
    paidQuotientDescentWrapperAvailable : Bool
    paidMonsterOccurrenceWrapperAvailable : Bool
    paidWholeSameObjectWrapperAvailable : Bool
    paidIndividualOrientationWrapperAvailable : Bool
    externalGapResultCreatesAgdaProof : Bool
    pairFamilyOccurrenceCreatesIndividualOrientation : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  false false false false false
  true true true true true true
  false false
