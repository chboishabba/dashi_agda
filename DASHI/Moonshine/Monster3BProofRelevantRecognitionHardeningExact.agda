module DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT HARDENING FOR THE MONSTER 3B RECOGNITION FRONTIER
--
-- Several older Monster interfaces correctly NAME their remaining obligations
-- but encode those obligations as fields whose values are themselves `Set`s.
-- Such a field records a proposition/type to be paid; it does not carry an
-- inhabitant of that proposition. This owner keeps the legacy APIs intact and
-- adds wrappers whose fields are inhabitants of those exact proposition types.
--
-- Repo-native cross-pollination: newer exact-review / causal-identification
-- owners use the same discipline -- typed obligation plus an inhabitant bound
-- to the same reviewed/identified object. No external source is needed for this
-- hardening; it is a DASHI interface correction.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact as Actual
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannMultiplicityExact as StoneMultiplicity
import DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact as Correction
import DASHI.Reasoning.Trialectic369SchrodingerHZetaRecognitionMaxCutExact as HZeta
import DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentSnowballExact as Constituent
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as Multiplicity
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom

------------------------------------------------------------------------
-- 1. H_zeta same-object recognition.
------------------------------------------------------------------------

record PaidSchrodingerIsActualHZeta
    (legacy : HZeta.SchrodingerIsActualHZeta) : Set₁ where
  field
    actualHZetaRecognitionWitness : HZeta.actualHZetaRecognition legacy
    actualHZetaActionIntertwinerWitness : HZeta.actualHZetaActionIntertwiner legacy

open PaidSchrodingerIsActualHZeta public

forgetPaidSchrodingerIsActualHZeta :
  (legacy : HZeta.SchrodingerIsActualHZeta) →
  PaidSchrodingerIsActualHZeta legacy →
  HZeta.SchrodingerIsActualHZeta
forgetPaidSchrodingerIsActualHZeta legacy paid = legacy

------------------------------------------------------------------------
-- 2. Stone--von Neumann constituent elements and lists.
--
-- `ZetaHeisenbergIrreducible` historically stores the TYPES
-- `selectedCentralCharacter` and `irreducible`.  A paid constituent must carry
-- inhabitants.  `AllPaidZetaHeisenbergIrreducibles` ties that payment to every
-- literal element of the decomposition list rather than to an unindexed global
-- proposition name.
------------------------------------------------------------------------

record PaidZetaHeisenbergIrreducible
    (constituent : StoneMultiplicity.ZetaHeisenbergIrreducible) : Set₁ where
  field
    selectedCentralCharacterWitness :
      StoneMultiplicity.selectedCentralCharacter constituent
    irreducibleWitness :
      StoneMultiplicity.irreducible constituent

open PaidZetaHeisenbergIrreducible public

data AllPaidZetaHeisenbergIrreducibles :
    List StoneMultiplicity.ZetaHeisenbergIrreducible → Set₁ where
  allPaidNil : AllPaidZetaHeisenbergIrreducibles []
  allPaidCons :
    {constituent : StoneMultiplicity.ZetaHeisenbergIrreducible} →
    {rest : List StoneMultiplicity.ZetaHeisenbergIrreducible} →
    PaidZetaHeisenbergIrreducible constituent →
    AllPaidZetaHeisenbergIrreducibles rest →
    AllPaidZetaHeisenbergIrreducibles (constituent ∷ rest)

------------------------------------------------------------------------
-- 3. Actual W_zeta|E constituent attachment.
------------------------------------------------------------------------

record PaidActualZetaConstituentAttachment
    {promotion : Actual.ActualKernelCharacterPromotion}
    (attachment : Constituent.ActualZetaConstituentAttachment promotion)
    : Set₁ where
  field
    constituentsPaid :
      AllPaidZetaHeisenbergIrreducibles
        (StoneMultiplicity.constituents (Constituent.decomposition attachment))

    sameActualRestrictedSectorWitness :
      Constituent.SameActualRestrictedSector attachment
    directSumRealisationWitness :
      Constituent.DirectSumRealisation attachment
    everyConstituentSelectedCentralPhaseWitness :
      Constituent.EveryConstituentSelectedCentralPhase attachment
    everyConstituentIrreducibleWitness :
      Constituent.EveryConstituentIrreducible attachment
    everyConstituentCharacterMatchesCanonicalSignatureWitness :
      Constituent.EveryConstituentCharacterMatchesCanonicalSignature attachment

open PaidActualZetaConstituentAttachment public

paidAttachmentMultiplicityIsNinety :
  {promotion : Actual.ActualKernelCharacterPromotion} →
  (attachment : Constituent.ActualZetaConstituentAttachment promotion) →
  PaidActualZetaConstituentAttachment attachment →
  StoneMultiplicity.constituentCount
    (StoneMultiplicity.constituents (Constituent.decomposition attachment))
    ≡ 90
paidAttachmentMultiplicityIsNinety attachment paid =
  Constituent.attachedMultiplicityIsNinety attachment

------------------------------------------------------------------------
-- 4. Linear multiplicity representation and canonical route.
------------------------------------------------------------------------

record PaidLinearMultiplicityRepresentation
    (linear : Multiplicity.LinearMultiplicityRepresentation) : Set₁ where
  field
    vectorDimensionIsNinetyWitness :
      Multiplicity.vectorDimensionIsNinety linear

open PaidLinearMultiplicityRepresentation public

record PaidCanonicalLinearMultiplicityRoute
    (route : Multiplicity.CanonicalLinearMultiplicityRoute) : Set₁ where
  field
    linearRepresentationPaid :
      PaidLinearMultiplicityRepresentation
        (Multiplicity.linearRepresentation route)
    sourcePaidTwelvePlusSeventyEightCharacterWitness :
      Multiplicity.sourcePaidTwelvePlusSeventyEightCharacter route
    sameObjectWithChosenZetaMultiplicityWitness :
      Multiplicity.sameObjectWithChosenZetaMultiplicity route
    linearEvaluationIntertwinerWitness :
      Multiplicity.linearEvaluationIntertwiner route

open PaidCanonicalLinearMultiplicityRoute public

------------------------------------------------------------------------
-- 5. Actual Hom-space/evaluation surface.
------------------------------------------------------------------------

record PaidActualLinearMultiplicityHomSpace
    (homSpace : Hom.ActualLinearMultiplicityHomSpace) : Set₁ where
  field
    sameLinearMultiplicityRepresentationPaid :
      PaidLinearMultiplicityRepresentation
        (Hom.sameObjectLinearRepresentation homSpace)
    sourcePaidCharacterOnSameMultiplicityWitness :
      Hom.sourcePaidCharacterOnSameMultiplicity homSpace
    evaluationIsLinearIntertwinerWitness :
      Hom.evaluationIsLinearIntertwiner homSpace

open PaidActualLinearMultiplicityHomSpace public

------------------------------------------------------------------------
-- 6. Corrected finite-basis recognition.
------------------------------------------------------------------------

record PaidActualZetaBasisRecognition
    {LiteralZetaSector : Set}
    (basis : Correction.ActualZetaBasisRecognition LiteralZetaSector)
    : Set₁ where
  field
    basisInclusionIsRepresentationNativeWitness :
      Correction.basisInclusionIsRepresentationNative basis

open PaidActualZetaBasisRecognition public

record PaidActualMultiplicityBasisRecognition
    {homSpace : Hom.ActualLinearMultiplicityHomSpace}
    (basis : Correction.ActualMultiplicityBasisRecognition homSpace)
    : Set₁ where
  field
    multiplicityBasisIsLinearBasisOfHomSpaceWitness :
      Correction.multiplicityBasisIsLinearBasisOfHomSpace basis
    normalizerActionOnMultiplicityBasisWitness :
      Correction.normalizerActionOnMultiplicityBasisPaid basis

open PaidActualMultiplicityBasisRecognition public

record PaidWZetaBasisVectorRecognition
    {LiteralZetaSector : Set}
    {homSpace : Hom.ActualLinearMultiplicityHomSpace}
    (recognition : Correction.WZetaBasisVectorRecognition LiteralZetaSector homSpace)
    : Set₁ where
  field
    zetaBasisRecognitionPaid :
      PaidActualZetaBasisRecognition (Correction.basisRecognition recognition)
    multiplicityBasisRecognitionPaid :
      PaidActualMultiplicityBasisRecognition
        (Correction.multiplicityBasisRecognition recognition)
    schrodingerBasisToX6Witness : Correction.schrodingerBasisToX6Paid recognition
    evaluationOfBasisTensorMatchesIncludedBasisWitness :
      Correction.evaluationOfBasisTensorMatchesIncludedBasis recognition
    translationActionExtendsLinearlyFromBasisWitness :
      Correction.translationActionExtendsLinearlyFromBasis recognition
    modulationActionExtendsLinearlyFromBasisWitness :
      Correction.modulationActionExtendsLinearlyFromBasis recognition

open PaidWZetaBasisVectorRecognition public

------------------------------------------------------------------------
-- 7. WrongType firewalls.
------------------------------------------------------------------------

data TypedObligationAloneCreatesRecognitionWitness : Set where
data CharacterTypeAloneCreatesCharacterWitness : Set where
data IntertwinerTypeAloneCreatesIntertwinerWitness : Set where
data SameObjectTypeAloneCreatesSameObjectWitness : Set where

typedObligationDoesNotCreateRecognitionWitness :
  TypedObligationAloneCreatesRecognitionWitness → ⊥
typedObligationDoesNotCreateRecognitionWitness ()

characterTypeDoesNotCreateCharacterWitness :
  CharacterTypeAloneCreatesCharacterWitness → ⊥
characterTypeDoesNotCreateCharacterWitness ()

intertwinerTypeDoesNotCreateIntertwinerWitness :
  IntertwinerTypeAloneCreatesIntertwinerWitness → ⊥
intertwinerTypeDoesNotCreateIntertwinerWitness ()

sameObjectTypeDoesNotCreateSameObjectWitness :
  SameObjectTypeAloneCreatesSameObjectWitness → ⊥
sameObjectTypeDoesNotCreateSameObjectWitness ()

------------------------------------------------------------------------
-- 8. Machine-readable audit boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    legacyHZetaRecognitionIsProofRelevant : Bool
    legacyMultiplicityDimensionIsProofRelevant : Bool
    legacyHomIntertwinerIsProofRelevant : Bool
    legacyConstituentElementIsProofRelevant : Bool
    legacyConstituentAttachmentIsProofRelevant : Bool
    legacyZetaBasisRecognitionIsProofRelevant : Bool
    legacyMultiplicityBasisRecognitionIsProofRelevant : Bool
    legacyWZetaBasisVectorRecognitionIsProofRelevant : Bool
    paidHZetaRecognitionWrapperAvailable : Bool
    paidMultiplicityRouteWrapperAvailable : Bool
    paidConstituentElementWrapperAvailable : Bool
    paidConstituentListWrapperAvailable : Bool
    paidConstituentAttachmentWrapperAvailable : Bool
    paidHomIntertwinerWrapperAvailable : Bool
    paidZetaBasisRecognitionWrapperAvailable : Bool
    paidMultiplicityBasisRecognitionWrapperAvailable : Bool
    paidWZetaBasisVectorRecognitionWrapperAvailable : Bool
    typedObligationAlonePaysRecognition : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  false false false false false false false false
  true true true true true true true true true
  false
