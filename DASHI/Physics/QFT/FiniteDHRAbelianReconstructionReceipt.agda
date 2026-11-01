module DASHI.Physics.QFT.FiniteDHRAbelianReconstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.U1CMOrbitIntegralReceipt as CM

------------------------------------------------------------------------
-- Finite abelian DHR reconstruction receipt.
--
-- This module records only a finite CM-character reconstruction surface:
-- the abelian dual group Z/4 x Z/6 x Z/2 and its componentwise character
-- product.  It deliberately does not construct a nonabelian Standard Model
-- gauge group, a full DHR category, Doplicher-Roberts reconstruction, or
-- G_DHR ~= G_SM.

data Z4Character : Set where
  z4-0 :
    Z4Character

  z4-1 :
    Z4Character

  z4-2 :
    Z4Character

  z4-3 :
    Z4Character

z4Successor :
  Z4Character →
  Z4Character
z4Successor z4-0 =
  z4-1
z4Successor z4-1 =
  z4-2
z4Successor z4-2 =
  z4-3
z4Successor z4-3 =
  z4-0

z4CharacterProduct :
  Z4Character →
  Z4Character →
  Z4Character
z4CharacterProduct z4-0 right =
  right
z4CharacterProduct z4-1 right =
  z4Successor right
z4CharacterProduct z4-2 right =
  z4Successor (z4Successor right)
z4CharacterProduct z4-3 right =
  z4Successor (z4Successor (z4Successor right))

data Z6Character : Set where
  z6-0 :
    Z6Character

  z6-1 :
    Z6Character

  z6-2 :
    Z6Character

  z6-3 :
    Z6Character

  z6-4 :
    Z6Character

  z6-5 :
    Z6Character

z6Successor :
  Z6Character →
  Z6Character
z6Successor z6-0 =
  z6-1
z6Successor z6-1 =
  z6-2
z6Successor z6-2 =
  z6-3
z6Successor z6-3 =
  z6-4
z6Successor z6-4 =
  z6-5
z6Successor z6-5 =
  z6-0

z6CharacterProduct :
  Z6Character →
  Z6Character →
  Z6Character
z6CharacterProduct z6-0 right =
  right
z6CharacterProduct z6-1 right =
  z6Successor right
z6CharacterProduct z6-2 right =
  z6Successor (z6Successor right)
z6CharacterProduct z6-3 right =
  z6Successor (z6Successor (z6Successor right))
z6CharacterProduct z6-4 right =
  z6Successor (z6Successor (z6Successor (z6Successor right)))
z6CharacterProduct z6-5 right =
  z6Successor
    (z6Successor (z6Successor (z6Successor (z6Successor right))))

data Z2Character : Set where
  z2-0 :
    Z2Character

  z2-1 :
    Z2Character

z2Successor :
  Z2Character →
  Z2Character
z2Successor z2-0 =
  z2-1
z2Successor z2-1 =
  z2-0

z2CharacterProduct :
  Z2Character →
  Z2Character →
  Z2Character
z2CharacterProduct z2-0 right =
  right
z2CharacterProduct z2-1 right =
  z2Successor right

record FiniteCMCharacter : Set where
  constructor cmCharacter
  field
    z4Component :
      Z4Character

    z6Component :
      Z6Character

    z2Component :
      Z2Character

open FiniteCMCharacter public

finiteCMCharacterProduct :
  FiniteCMCharacter →
  FiniteCMCharacter →
  FiniteCMCharacter
finiteCMCharacterProduct left right =
  cmCharacter
    (z4CharacterProduct (z4Component left) (z4Component right))
    (z6CharacterProduct (z6Component left) (z6Component right))
    (z2CharacterProduct (z2Component left) (z2Component right))

trivialFiniteCMCharacter :
  FiniteCMCharacter
trivialFiniteCMCharacter =
  cmCharacter z4-0 z6-0 z2-0

p2CMCharacter :
  FiniteCMCharacter
p2CMCharacter =
  cmCharacter z4-1 z6-0 z2-0

p3CMCharacter :
  FiniteCMCharacter
p3CMCharacter =
  cmCharacter z4-0 z6-1 z2-0

p5CMCharacter :
  FiniteCMCharacter
p5CMCharacter =
  cmCharacter z4-0 z6-0 z2-1

p2p3CMCharacter :
  FiniteCMCharacter
p2p3CMCharacter =
  finiteCMCharacterProduct p2CMCharacter p3CMCharacter

p2p5CMCharacter :
  FiniteCMCharacter
p2p5CMCharacter =
  finiteCMCharacterProduct p2CMCharacter p5CMCharacter

p3p5CMCharacter :
  FiniteCMCharacter
p3p5CMCharacter =
  finiteCMCharacterProduct p3CMCharacter p5CMCharacter

allGeneratorProductCharacters :
  List FiniteCMCharacter
allGeneratorProductCharacters =
  p2p3CMCharacter
  ∷ p2p5CMCharacter
  ∷ p3p5CMCharacter
  ∷ []

data FiniteDHRAbelianDualFactor : Set where
  z4CMConductorFactor :
    FiniteDHRAbelianDualFactor

  z6CMVolumeFactor :
    FiniteDHRAbelianDualFactor

  z2ParityFactor :
    FiniteDHRAbelianDualFactor

finiteDHRAbelianDualFactorOrder :
  FiniteDHRAbelianDualFactor →
  Nat
finiteDHRAbelianDualFactorOrder z4CMConductorFactor =
  4
finiteDHRAbelianDualFactorOrder z6CMVolumeFactor =
  6
finiteDHRAbelianDualFactorOrder z2ParityFactor =
  2

canonicalFiniteDHRAbelianDualFactors :
  List FiniteDHRAbelianDualFactor
canonicalFiniteDHRAbelianDualFactors =
  z4CMConductorFactor
  ∷ z6CMVolumeFactor
  ∷ z2ParityFactor
  ∷ []

data FiniteDHRAbelianReconstructionStatus : Set where
  finiteAbelianCMCharacterSurfaceOnly :
    FiniteDHRAbelianReconstructionStatus

finiteAbelianDualGroupLabel : String
finiteAbelianDualGroupLabel =
  "Z/4 x Z/6 x Z/2"

finiteCharacterProductLabel : String
finiteCharacterProductLabel =
  "componentwise addition of CM characters in Z/4 x Z/6 x Z/2"

b4TensorFusionReceiptPathLabel : String
b4TensorFusionReceiptPathLabel =
  "DASHI.Physics.QFT.FinitePrimeLaneTensorFusionReceipts.canonicalFinitePrimeLaneTensorFusionReceipt"

record FiniteDHRAbelianReconstructionReceipt : Setω where
  field
    status :
      FiniteDHRAbelianReconstructionStatus

    cmOrbitIntegralReceipt :
      CM.U1CMOrbitIntegralReceipt

    cmOrbitIntegralReceiptReferenced :
      Bool

    cmOrbitIntegralReceiptReferencedIsTrue :
      cmOrbitIntegralReceiptReferenced ≡ true

    b4TensorFusionReceiptPath :
      String

    b4TensorFusionReceiptPathIsCanonical :
      b4TensorFusionReceiptPath ≡ b4TensorFusionReceiptPathLabel

    b4TensorFusionReceiptReferenced :
      Bool

    b4TensorFusionReceiptReferencedIsTrue :
      b4TensorFusionReceiptReferenced ≡ true

    dualGroupLabel :
      String

    dualGroupLabelIsCanonical :
      dualGroupLabel ≡ finiteAbelianDualGroupLabel

    dualFactors :
      List FiniteDHRAbelianDualFactor

    dualFactorsAreCanonical :
      dualFactors ≡ canonicalFiniteDHRAbelianDualFactors

    z4FactorOrder :
      Nat

    z4FactorOrderIsFour :
      z4FactorOrder ≡ finiteDHRAbelianDualFactorOrder z4CMConductorFactor

    z6FactorOrder :
      Nat

    z6FactorOrderIsSix :
      z6FactorOrder ≡ finiteDHRAbelianDualFactorOrder z6CMVolumeFactor

    z2FactorOrder :
      Nat

    z2FactorOrderIsTwo :
      z2FactorOrder ≡ finiteDHRAbelianDualFactorOrder z2ParityFactor

    trivialCharacter :
      FiniteCMCharacter

    trivialCharacterIsCanonical :
      trivialCharacter ≡ trivialFiniteCMCharacter

    p2Character :
      FiniteCMCharacter

    p2CharacterIsCanonical :
      p2Character ≡ p2CMCharacter

    p3Character :
      FiniteCMCharacter

    p3CharacterIsCanonical :
      p3Character ≡ p3CMCharacter

    p5Character :
      FiniteCMCharacter

    p5CharacterIsCanonical :
      p5Character ≡ p5CMCharacter

    characterProduct :
      FiniteCMCharacter →
      FiniteCMCharacter →
      FiniteCMCharacter

    characterProductIsCanonical :
      characterProduct ≡ finiteCMCharacterProduct

    p2p3Product :
      characterProduct p2Character p3Character ≡ p2p3CMCharacter

    p2p5Product :
      characterProduct p2Character p5Character ≡ p2p5CMCharacter

    p3p5Product :
      characterProduct p3Character p5Character ≡ p3p5CMCharacter

    generatorProductCharacters :
      List FiniteCMCharacter

    generatorProductCharactersAreCanonical :
      generatorProductCharacters ≡ allGeneratorProductCharacters

    characterProductLabel :
      String

    characterProductLabelIsCanonical :
      characterProductLabel ≡ finiteCharacterProductLabel

    finiteAbelianDualGroupReconstructed :
      Bool

    finiteAbelianDualGroupReconstructedIsTrue :
      finiteAbelianDualGroupReconstructed ≡ true

    finiteCharacterProductSurfaceConstructed :
      Bool

    finiteCharacterProductSurfaceConstructedIsTrue :
      finiteCharacterProductSurfaceConstructed ≡ true

    nonabelianStandardModelGaugeGroupReconstructed :
      Bool

    nonabelianStandardModelGaugeGroupReconstructedIsFalse :
      nonabelianStandardModelGaugeGroupReconstructed ≡ false

    fullDHRDRReconstructionConstructed :
      Bool

    fullDHRDRReconstructionConstructedIsFalse :
      fullDHRDRReconstructionConstructed ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    receiptBoundary :
      List String

open FiniteDHRAbelianReconstructionReceipt public

canonicalFiniteDHRAbelianReconstructionReceipt :
  FiniteDHRAbelianReconstructionReceipt
canonicalFiniteDHRAbelianReconstructionReceipt =
  record
    { status =
        finiteAbelianCMCharacterSurfaceOnly
    ; cmOrbitIntegralReceipt =
        CM.canonicalU1CMOrbitIntegralReceipt
    ; cmOrbitIntegralReceiptReferenced =
        true
    ; cmOrbitIntegralReceiptReferencedIsTrue =
        refl
    ; b4TensorFusionReceiptPath =
        b4TensorFusionReceiptPathLabel
    ; b4TensorFusionReceiptPathIsCanonical =
        refl
    ; b4TensorFusionReceiptReferenced =
        true
    ; b4TensorFusionReceiptReferencedIsTrue =
        refl
    ; dualGroupLabel =
        finiteAbelianDualGroupLabel
    ; dualGroupLabelIsCanonical =
        refl
    ; dualFactors =
        canonicalFiniteDHRAbelianDualFactors
    ; dualFactorsAreCanonical =
        refl
    ; z4FactorOrder =
        4
    ; z4FactorOrderIsFour =
        refl
    ; z6FactorOrder =
        6
    ; z6FactorOrderIsSix =
        refl
    ; z2FactorOrder =
        2
    ; z2FactorOrderIsTwo =
        refl
    ; trivialCharacter =
        trivialFiniteCMCharacter
    ; trivialCharacterIsCanonical =
        refl
    ; p2Character =
        p2CMCharacter
    ; p2CharacterIsCanonical =
        refl
    ; p3Character =
        p3CMCharacter
    ; p3CharacterIsCanonical =
        refl
    ; p5Character =
        p5CMCharacter
    ; p5CharacterIsCanonical =
        refl
    ; characterProduct =
        finiteCMCharacterProduct
    ; characterProductIsCanonical =
        refl
    ; p2p3Product =
        refl
    ; p2p5Product =
        refl
    ; p3p5Product =
        refl
    ; generatorProductCharacters =
        allGeneratorProductCharacters
    ; generatorProductCharactersAreCanonical =
        refl
    ; characterProductLabel =
        finiteCharacterProductLabel
    ; characterProductLabelIsCanonical =
        refl
    ; finiteAbelianDualGroupReconstructed =
        true
    ; finiteAbelianDualGroupReconstructedIsTrue =
        refl
    ; finiteCharacterProductSurfaceConstructed =
        true
    ; finiteCharacterProductSurfaceConstructedIsTrue =
        refl
    ; nonabelianStandardModelGaugeGroupReconstructed =
        false
    ; nonabelianStandardModelGaugeGroupReconstructedIsFalse =
        refl
    ; fullDHRDRReconstructionConstructed =
        false
    ; fullDHRDRReconstructionConstructedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Finite abelian dual group recorded: Z/4 x Z/6 x Z/2"
        ∷ "The character product is componentwise over the three finite cyclic factors"
        ∷ "The receipt references the current U1 CM orbit-integral receipt and B4 finite tensor-fusion receipt"
        ∷ "This is a finite abelian CM-character surface only"
        ∷ "No nonabelian Standard Model gauge group, full DR reconstruction, or G_DHR ~= G_SM promotion is constructed"
        ∷ []
    }

finiteDHRAbelianReceiptReconstructsFiniteDualGroup :
  finiteAbelianDualGroupReconstructed
    canonicalFiniteDHRAbelianReconstructionReceipt
  ≡
  true
finiteDHRAbelianReceiptReconstructsFiniteDualGroup =
  refl

finiteDHRAbelianReceiptConstructsCharacterProductSurface :
  finiteCharacterProductSurfaceConstructed
    canonicalFiniteDHRAbelianReconstructionReceipt
  ≡
  true
finiteDHRAbelianReceiptConstructsCharacterProductSurface =
  refl

finiteDHRAbelianReceiptKeepsNonabelianSMFalse :
  nonabelianStandardModelGaugeGroupReconstructed
    canonicalFiniteDHRAbelianReconstructionReceipt
  ≡
  false
finiteDHRAbelianReceiptKeepsNonabelianSMFalse =
  refl

finiteDHRAbelianReceiptKeepsFullDRFalse :
  fullDHRDRReconstructionConstructed
    canonicalFiniteDHRAbelianReconstructionReceipt
  ≡
  false
finiteDHRAbelianReceiptKeepsFullDRFalse =
  refl

finiteDHRAbelianReceiptKeepsGDHREqualsGSMFalse :
  gDHREqualsGSMPromoted canonicalFiniteDHRAbelianReconstructionReceipt
  ≡
  false
finiteDHRAbelianReceiptKeepsGDHREqualsGSMFalse =
  refl

finiteDHRAbelianReceiptReferencesB4TensorFusion :
  b4TensorFusionReceiptReferenced canonicalFiniteDHRAbelianReconstructionReceipt
  ≡
  true
finiteDHRAbelianReceiptReferencesB4TensorFusion =
  refl

finiteDHRAbelianReceiptReferencesCMOrbitIntegral :
  cmOrbitIntegralReceiptReferenced
    canonicalFiniteDHRAbelianReconstructionReceipt
  ≡
  true
finiteDHRAbelianReceiptReferencesCMOrbitIntegral =
  refl
