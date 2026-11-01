module DASHI.Physics.Closure.MatterRepresentationReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Moonshine
import DASHI.Physics.Closure.FractranPrimeLaneValuationReceiptSurface as FractranLane
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR

------------------------------------------------------------------------
-- Standard Model matter-representation receipt surface.
--
-- This module records target sockets for deriving or adapting Standard Model
-- matter representations, plus local constructor witnesses for the Higgs
-- doublet and left-quark doublet family.  It does not derive the Standard
-- Model group, hypercharge assignments, anomaly cancellation, generations,
-- Yukawa matrices, CKM/PMNS mixing, neutrino sector, or a GRQFT/TOE receipt.

data MatterRepresentationSurfaceStatus : Set where
  matterRepresentationTargetsOnlyNoPromotion :
    MatterRepresentationSurfaceStatus

data MatterRepresentationPromotionAuthorityToken : Set where

data MatterPrimeLaneTarget : Set where
  matterPrimeLaneDHRLocalizedEndomorphismTarget :
    MatterPrimeLaneTarget

  matterPrimeLaneTransportabilityTarget :
    MatterPrimeLaneTarget

  matterPrimeLaneSectorRepresentationTarget :
    MatterPrimeLaneTarget

  matterPrimeLaneDimensionConjectureTarget :
    MatterPrimeLaneTarget

canonicalMatterPrimeLaneTargets :
  List MatterPrimeLaneTarget
canonicalMatterPrimeLaneTargets =
  matterPrimeLaneDHRLocalizedEndomorphismTarget
  ∷ matterPrimeLaneTransportabilityTarget
  ∷ matterPrimeLaneSectorRepresentationTarget
  ∷ matterPrimeLaneDimensionConjectureTarget
  ∷ []

data StandardModelMatterSectorTarget : Set where
  leftQuarkDoubletTarget :
    StandardModelMatterSectorTarget

  rightUpQuarkTarget :
    StandardModelMatterSectorTarget

  rightDownQuarkTarget :
    StandardModelMatterSectorTarget

  leftLeptonDoubletTarget :
    StandardModelMatterSectorTarget

  rightChargedLeptonTarget :
    StandardModelMatterSectorTarget

  higgsDoubletTarget :
    StandardModelMatterSectorTarget

canonicalStandardModelMatterSectorTargets :
  List StandardModelMatterSectorTarget
canonicalStandardModelMatterSectorTargets =
  leftQuarkDoubletTarget
  ∷ rightUpQuarkTarget
  ∷ rightDownQuarkTarget
  ∷ leftLeptonDoubletTarget
  ∷ rightChargedLeptonTarget
  ∷ higgsDoubletTarget
  ∷ []

data GaugeRepresentationFactor : Set where
  su3ColourFactor :
    GaugeRepresentationFactor

  su2LWeakFactor :
    GaugeRepresentationFactor

  u1YHyperchargeFactor :
    GaugeRepresentationFactor

data GaugeRepresentationDimension : Set where
  representationDimensionOne :
    GaugeRepresentationDimension

  representationDimensionTwo :
    GaugeRepresentationDimension

  representationDimensionThree :
    GaugeRepresentationDimension

record GaugeRepresentationPrimitive : Set where
  constructor gaugeRepresentationPrimitive
  field
    gaugeRepresentationFactor :
      GaugeRepresentationFactor

    gaugeRepresentationDimension :
      GaugeRepresentationDimension

    gaugeRepresentationLabel :
      String

open GaugeRepresentationPrimitive public

canonicalSU3ColourTripletPrimitive :
  GaugeRepresentationPrimitive
canonicalSU3ColourTripletPrimitive =
  record
    { gaugeRepresentationFactor =
        su3ColourFactor
    ; gaugeRepresentationDimension =
        representationDimensionThree
    ; gaugeRepresentationLabel =
        "SU3_c triplet"
    }

canonicalSU2LWeakDoubletPrimitive :
  GaugeRepresentationPrimitive
canonicalSU2LWeakDoubletPrimitive =
  record
    { gaugeRepresentationFactor =
        su2LWeakFactor
    ; gaugeRepresentationDimension =
        representationDimensionTwo
    ; gaugeRepresentationLabel =
        "SU2_L doublet"
    }

canonicalSU3ColourSingletPrimitive :
  GaugeRepresentationPrimitive
canonicalSU3ColourSingletPrimitive =
  record
    { gaugeRepresentationFactor =
        su3ColourFactor
    ; gaugeRepresentationDimension =
        representationDimensionOne
    ; gaugeRepresentationLabel =
        "SU3_c singlet"
    }

canonicalSU2LWeakSingletPrimitive :
  GaugeRepresentationPrimitive
canonicalSU2LWeakSingletPrimitive =
  record
    { gaugeRepresentationFactor =
        su2LWeakFactor
    ; gaugeRepresentationDimension =
        representationDimensionOne
    ; gaugeRepresentationLabel =
        "SU2_L singlet"
    }

record HyperchargePrimitive : Set where
  constructor hyperchargePrimitive
  field
    hyperchargeNumerator :
      Nat

    hyperchargeDenominator :
      Nat

    hyperchargePositive :
      Bool

    hyperchargeLabel :
      String

open HyperchargePrimitive public

canonicalHyperchargePlusOnePrimitive :
  HyperchargePrimitive
canonicalHyperchargePlusOnePrimitive =
  record
    { hyperchargeNumerator =
        1
    ; hyperchargeDenominator =
        1
    ; hyperchargePositive =
        true
    ; hyperchargeLabel =
        "Y=+1"
    }

canonicalHyperchargeOneSixthPrimitive :
  HyperchargePrimitive
canonicalHyperchargeOneSixthPrimitive =
  record
    { hyperchargeNumerator =
        1
    ; hyperchargeDenominator =
        6
    ; hyperchargePositive =
        true
    ; hyperchargeLabel =
        "Y=+1/6"
    }

canonicalHyperchargeTwoThirdsPrimitive :
  HyperchargePrimitive
canonicalHyperchargeTwoThirdsPrimitive =
  record
    { hyperchargeNumerator =
        2
    ; hyperchargeDenominator =
        3
    ; hyperchargePositive =
        true
    ; hyperchargeLabel =
        "Y=+2/3"
    }

canonicalHyperchargeMinusOneThirdPrimitive :
  HyperchargePrimitive
canonicalHyperchargeMinusOneThirdPrimitive =
  record
    { hyperchargeNumerator =
        1
    ; hyperchargeDenominator =
        3
    ; hyperchargePositive =
        false
    ; hyperchargeLabel =
        "Y=-1/3"
    }

canonicalHyperchargeMinusOneHalfPrimitive :
  HyperchargePrimitive
canonicalHyperchargeMinusOneHalfPrimitive =
  record
    { hyperchargeNumerator =
        1
    ; hyperchargeDenominator =
        2
    ; hyperchargePositive =
        false
    ; hyperchargeLabel =
        "Y=-1/2"
    }

canonicalHyperchargeMinusOnePrimitive :
  HyperchargePrimitive
canonicalHyperchargeMinusOnePrimitive =
  record
    { hyperchargeNumerator =
        1
    ; hyperchargeDenominator =
        1
    ; hyperchargePositive =
        false
    ; hyperchargeLabel =
        "Y=-1"
    }

data ChiralityPrimitive : Set where
  scalarChirality :
    ChiralityPrimitive

  leftChirality :
    ChiralityPrimitive

  rightChirality :
    ChiralityPrimitive

record ComponentPrimitive : Set where
  constructor componentPrimitive
  field
    componentCount :
      Nat

    componentLabel :
      String

open ComponentPrimitive public

canonicalHiggsFourRealComponentPrimitive :
  ComponentPrimitive
canonicalHiggsFourRealComponentPrimitive =
  record
    { componentCount =
        4
    ; componentLabel =
        "four real Higgs components"
    }

canonicalLeftQuarkSixColourWeakComponentPrimitive :
  ComponentPrimitive
canonicalLeftQuarkSixColourWeakComponentPrimitive =
  record
    { componentCount =
        6
    ; componentLabel =
        "three colour times two weak components per generation"
    }

canonicalRightQuarkThreeColourComponentPrimitive :
  ComponentPrimitive
canonicalRightQuarkThreeColourComponentPrimitive =
  record
    { componentCount =
        3
    ; componentLabel =
        "three colour components per generation"
    }

canonicalLeftLeptonTwoWeakComponentPrimitive :
  ComponentPrimitive
canonicalLeftLeptonTwoWeakComponentPrimitive =
  record
    { componentCount =
        2
    ; componentLabel =
        "two weak components per generation"
    }

canonicalRightLeptonOneComponentPrimitive :
  ComponentPrimitive
canonicalRightLeptonOneComponentPrimitive =
  record
    { componentCount =
        1
    ; componentLabel =
        "one charged lepton component per generation"
    }

record GenerationPrimitive : Set where
  constructor generationPrimitive
  field
    generationCount :
      Nat

    generationLabel :
      String

open GenerationPrimitive public

canonicalThreeGenerationPrimitive :
  GenerationPrimitive
canonicalThreeGenerationPrimitive =
  record
    { generationCount =
        3
    ; generationLabel =
        "three generations"
    }

record HiggsDoubletPrimitive : Set where
  constructor higgsDoubletPrimitive
  field
    higgsPrimitiveMatterSector :
      StandardModelMatterSectorTarget

    higgsPrimitiveMatterSectorIsHiggsDoublet :
      higgsPrimitiveMatterSector
      ≡
      higgsDoubletTarget

    higgsPrimitiveWeakRepresentation :
      GaugeRepresentationPrimitive

    higgsPrimitiveWeakRepresentationIsSU2LDoublet :
      higgsPrimitiveWeakRepresentation
      ≡
      canonicalSU2LWeakDoubletPrimitive

    higgsPrimitiveHypercharge :
      HyperchargePrimitive

    higgsPrimitiveHyperchargeIsPlusOne :
      higgsPrimitiveHypercharge
      ≡
      canonicalHyperchargePlusOnePrimitive

    higgsPrimitiveChirality :
      ChiralityPrimitive

    higgsPrimitiveChiralityIsScalar :
      higgsPrimitiveChirality
      ≡
      scalarChirality

    higgsPrimitiveComponents :
      ComponentPrimitive

    higgsPrimitiveComponentsAreFourReal :
      higgsPrimitiveComponents
      ≡
      canonicalHiggsFourRealComponentPrimitive

open HiggsDoubletPrimitive public

canonicalHiggsDoubletPrimitive :
  HiggsDoubletPrimitive
canonicalHiggsDoubletPrimitive =
  record
    { higgsPrimitiveMatterSector =
        higgsDoubletTarget
    ; higgsPrimitiveMatterSectorIsHiggsDoublet =
        refl
    ; higgsPrimitiveWeakRepresentation =
        canonicalSU2LWeakDoubletPrimitive
    ; higgsPrimitiveWeakRepresentationIsSU2LDoublet =
        refl
    ; higgsPrimitiveHypercharge =
        canonicalHyperchargePlusOnePrimitive
    ; higgsPrimitiveHyperchargeIsPlusOne =
        refl
    ; higgsPrimitiveChirality =
        scalarChirality
    ; higgsPrimitiveChiralityIsScalar =
        refl
    ; higgsPrimitiveComponents =
        canonicalHiggsFourRealComponentPrimitive
    ; higgsPrimitiveComponentsAreFourReal =
        refl
    }

record LeftQuarkDoubletFamilyPrimitive : Set where
  constructor leftQuarkDoubletFamilyPrimitive
  field
    leftQuarkPrimitiveMatterSector :
      StandardModelMatterSectorTarget

    leftQuarkPrimitiveMatterSectorIsLeftQuarkDoublet :
      leftQuarkPrimitiveMatterSector
      ≡
      leftQuarkDoubletTarget

    leftQuarkPrimitiveColourRepresentation :
      GaugeRepresentationPrimitive

    leftQuarkPrimitiveColourRepresentationIsSU3Triplet :
      leftQuarkPrimitiveColourRepresentation
      ≡
      canonicalSU3ColourTripletPrimitive

    leftQuarkPrimitiveWeakRepresentation :
      GaugeRepresentationPrimitive

    leftQuarkPrimitiveWeakRepresentationIsSU2LDoublet :
      leftQuarkPrimitiveWeakRepresentation
      ≡
      canonicalSU2LWeakDoubletPrimitive

    leftQuarkPrimitiveHypercharge :
      HyperchargePrimitive

    leftQuarkPrimitiveHyperchargeIsOneSixth :
      leftQuarkPrimitiveHypercharge
      ≡
      canonicalHyperchargeOneSixthPrimitive

    leftQuarkPrimitiveChirality :
      ChiralityPrimitive

    leftQuarkPrimitiveChiralityIsLeft :
      leftQuarkPrimitiveChirality
      ≡
      leftChirality

    leftQuarkPrimitiveComponents :
      ComponentPrimitive

    leftQuarkPrimitiveComponentsAreColourWeakSix :
      leftQuarkPrimitiveComponents
      ≡
      canonicalLeftQuarkSixColourWeakComponentPrimitive

    leftQuarkPrimitiveGenerations :
      GenerationPrimitive

    leftQuarkPrimitiveGenerationsAreThree :
      leftQuarkPrimitiveGenerations
      ≡
      canonicalThreeGenerationPrimitive

open LeftQuarkDoubletFamilyPrimitive public

canonicalLeftQuarkDoubletFamilyPrimitive :
  LeftQuarkDoubletFamilyPrimitive
canonicalLeftQuarkDoubletFamilyPrimitive =
  record
    { leftQuarkPrimitiveMatterSector =
        leftQuarkDoubletTarget
    ; leftQuarkPrimitiveMatterSectorIsLeftQuarkDoublet =
        refl
    ; leftQuarkPrimitiveColourRepresentation =
        canonicalSU3ColourTripletPrimitive
    ; leftQuarkPrimitiveColourRepresentationIsSU3Triplet =
        refl
    ; leftQuarkPrimitiveWeakRepresentation =
        canonicalSU2LWeakDoubletPrimitive
    ; leftQuarkPrimitiveWeakRepresentationIsSU2LDoublet =
        refl
    ; leftQuarkPrimitiveHypercharge =
        canonicalHyperchargeOneSixthPrimitive
    ; leftQuarkPrimitiveHyperchargeIsOneSixth =
        refl
    ; leftQuarkPrimitiveChirality =
        leftChirality
    ; leftQuarkPrimitiveChiralityIsLeft =
        refl
    ; leftQuarkPrimitiveComponents =
        canonicalLeftQuarkSixColourWeakComponentPrimitive
    ; leftQuarkPrimitiveComponentsAreColourWeakSix =
        refl
    ; leftQuarkPrimitiveGenerations =
        canonicalThreeGenerationPrimitive
    ; leftQuarkPrimitiveGenerationsAreThree =
        refl
    }

record RightUpQuarkFamilyPrimitive : Set where
  constructor rightUpQuarkFamilyPrimitive
  field
    rightUpQuarkPrimitiveMatterSector :
      StandardModelMatterSectorTarget

    rightUpQuarkPrimitiveMatterSectorIsRightUpQuark :
      rightUpQuarkPrimitiveMatterSector
      ≡
      rightUpQuarkTarget

    rightUpQuarkPrimitiveColourRepresentation :
      GaugeRepresentationPrimitive

    rightUpQuarkPrimitiveColourRepresentationIsSU3Triplet :
      rightUpQuarkPrimitiveColourRepresentation
      ≡
      canonicalSU3ColourTripletPrimitive

    rightUpQuarkPrimitiveWeakRepresentation :
      GaugeRepresentationPrimitive

    rightUpQuarkPrimitiveWeakRepresentationIsSU2LSinglet :
      rightUpQuarkPrimitiveWeakRepresentation
      ≡
      canonicalSU2LWeakSingletPrimitive

    rightUpQuarkPrimitiveHypercharge :
      HyperchargePrimitive

    rightUpQuarkPrimitiveHyperchargeIsTwoThirds :
      rightUpQuarkPrimitiveHypercharge
      ≡
      canonicalHyperchargeTwoThirdsPrimitive

    rightUpQuarkPrimitiveChirality :
      ChiralityPrimitive

    rightUpQuarkPrimitiveChiralityIsRight :
      rightUpQuarkPrimitiveChirality
      ≡
      rightChirality

    rightUpQuarkPrimitiveComponents :
      ComponentPrimitive

    rightUpQuarkPrimitiveComponentsAreThreeColour :
      rightUpQuarkPrimitiveComponents
      ≡
      canonicalRightQuarkThreeColourComponentPrimitive

    rightUpQuarkPrimitiveGenerations :
      GenerationPrimitive

    rightUpQuarkPrimitiveGenerationsAreThree :
      rightUpQuarkPrimitiveGenerations
      ≡
      canonicalThreeGenerationPrimitive

open RightUpQuarkFamilyPrimitive public

canonicalRightUpQuarkFamilyPrimitive :
  RightUpQuarkFamilyPrimitive
canonicalRightUpQuarkFamilyPrimitive =
  record
    { rightUpQuarkPrimitiveMatterSector =
        rightUpQuarkTarget
    ; rightUpQuarkPrimitiveMatterSectorIsRightUpQuark =
        refl
    ; rightUpQuarkPrimitiveColourRepresentation =
        canonicalSU3ColourTripletPrimitive
    ; rightUpQuarkPrimitiveColourRepresentationIsSU3Triplet =
        refl
    ; rightUpQuarkPrimitiveWeakRepresentation =
        canonicalSU2LWeakSingletPrimitive
    ; rightUpQuarkPrimitiveWeakRepresentationIsSU2LSinglet =
        refl
    ; rightUpQuarkPrimitiveHypercharge =
        canonicalHyperchargeTwoThirdsPrimitive
    ; rightUpQuarkPrimitiveHyperchargeIsTwoThirds =
        refl
    ; rightUpQuarkPrimitiveChirality =
        rightChirality
    ; rightUpQuarkPrimitiveChiralityIsRight =
        refl
    ; rightUpQuarkPrimitiveComponents =
        canonicalRightQuarkThreeColourComponentPrimitive
    ; rightUpQuarkPrimitiveComponentsAreThreeColour =
        refl
    ; rightUpQuarkPrimitiveGenerations =
        canonicalThreeGenerationPrimitive
    ; rightUpQuarkPrimitiveGenerationsAreThree =
        refl
    }

record RightDownQuarkFamilyPrimitive : Set where
  constructor rightDownQuarkFamilyPrimitive
  field
    rightDownQuarkPrimitiveMatterSector :
      StandardModelMatterSectorTarget

    rightDownQuarkPrimitiveMatterSectorIsRightDownQuark :
      rightDownQuarkPrimitiveMatterSector
      ≡
      rightDownQuarkTarget

    rightDownQuarkPrimitiveColourRepresentation :
      GaugeRepresentationPrimitive

    rightDownQuarkPrimitiveColourRepresentationIsSU3Triplet :
      rightDownQuarkPrimitiveColourRepresentation
      ≡
      canonicalSU3ColourTripletPrimitive

    rightDownQuarkPrimitiveWeakRepresentation :
      GaugeRepresentationPrimitive

    rightDownQuarkPrimitiveWeakRepresentationIsSU2LSinglet :
      rightDownQuarkPrimitiveWeakRepresentation
      ≡
      canonicalSU2LWeakSingletPrimitive

    rightDownQuarkPrimitiveHypercharge :
      HyperchargePrimitive

    rightDownQuarkPrimitiveHyperchargeIsMinusOneThird :
      rightDownQuarkPrimitiveHypercharge
      ≡
      canonicalHyperchargeMinusOneThirdPrimitive

    rightDownQuarkPrimitiveChirality :
      ChiralityPrimitive

    rightDownQuarkPrimitiveChiralityIsRight :
      rightDownQuarkPrimitiveChirality
      ≡
      rightChirality

    rightDownQuarkPrimitiveComponents :
      ComponentPrimitive

    rightDownQuarkPrimitiveComponentsAreThreeColour :
      rightDownQuarkPrimitiveComponents
      ≡
      canonicalRightQuarkThreeColourComponentPrimitive

    rightDownQuarkPrimitiveGenerations :
      GenerationPrimitive

    rightDownQuarkPrimitiveGenerationsAreThree :
      rightDownQuarkPrimitiveGenerations
      ≡
      canonicalThreeGenerationPrimitive

open RightDownQuarkFamilyPrimitive public

canonicalRightDownQuarkFamilyPrimitive :
  RightDownQuarkFamilyPrimitive
canonicalRightDownQuarkFamilyPrimitive =
  record
    { rightDownQuarkPrimitiveMatterSector =
        rightDownQuarkTarget
    ; rightDownQuarkPrimitiveMatterSectorIsRightDownQuark =
        refl
    ; rightDownQuarkPrimitiveColourRepresentation =
        canonicalSU3ColourTripletPrimitive
    ; rightDownQuarkPrimitiveColourRepresentationIsSU3Triplet =
        refl
    ; rightDownQuarkPrimitiveWeakRepresentation =
        canonicalSU2LWeakSingletPrimitive
    ; rightDownQuarkPrimitiveWeakRepresentationIsSU2LSinglet =
        refl
    ; rightDownQuarkPrimitiveHypercharge =
        canonicalHyperchargeMinusOneThirdPrimitive
    ; rightDownQuarkPrimitiveHyperchargeIsMinusOneThird =
        refl
    ; rightDownQuarkPrimitiveChirality =
        rightChirality
    ; rightDownQuarkPrimitiveChiralityIsRight =
        refl
    ; rightDownQuarkPrimitiveComponents =
        canonicalRightQuarkThreeColourComponentPrimitive
    ; rightDownQuarkPrimitiveComponentsAreThreeColour =
        refl
    ; rightDownQuarkPrimitiveGenerations =
        canonicalThreeGenerationPrimitive
    ; rightDownQuarkPrimitiveGenerationsAreThree =
        refl
    }

record LeftLeptonDoubletFamilyPrimitive : Set where
  constructor leftLeptonDoubletFamilyPrimitive
  field
    leftLeptonPrimitiveMatterSector :
      StandardModelMatterSectorTarget

    leftLeptonPrimitiveMatterSectorIsLeftLeptonDoublet :
      leftLeptonPrimitiveMatterSector
      ≡
      leftLeptonDoubletTarget

    leftLeptonPrimitiveColourRepresentation :
      GaugeRepresentationPrimitive

    leftLeptonPrimitiveColourRepresentationIsSU3Singlet :
      leftLeptonPrimitiveColourRepresentation
      ≡
      canonicalSU3ColourSingletPrimitive

    leftLeptonPrimitiveWeakRepresentation :
      GaugeRepresentationPrimitive

    leftLeptonPrimitiveWeakRepresentationIsSU2LDoublet :
      leftLeptonPrimitiveWeakRepresentation
      ≡
      canonicalSU2LWeakDoubletPrimitive

    leftLeptonPrimitiveHypercharge :
      HyperchargePrimitive

    leftLeptonPrimitiveHyperchargeIsMinusOneHalf :
      leftLeptonPrimitiveHypercharge
      ≡
      canonicalHyperchargeMinusOneHalfPrimitive

    leftLeptonPrimitiveChirality :
      ChiralityPrimitive

    leftLeptonPrimitiveChiralityIsLeft :
      leftLeptonPrimitiveChirality
      ≡
      leftChirality

    leftLeptonPrimitiveComponents :
      ComponentPrimitive

    leftLeptonPrimitiveComponentsAreTwoWeak :
      leftLeptonPrimitiveComponents
      ≡
      canonicalLeftLeptonTwoWeakComponentPrimitive

    leftLeptonPrimitiveGenerations :
      GenerationPrimitive

    leftLeptonPrimitiveGenerationsAreThree :
      leftLeptonPrimitiveGenerations
      ≡
      canonicalThreeGenerationPrimitive

open LeftLeptonDoubletFamilyPrimitive public

canonicalLeftLeptonDoubletFamilyPrimitive :
  LeftLeptonDoubletFamilyPrimitive
canonicalLeftLeptonDoubletFamilyPrimitive =
  record
    { leftLeptonPrimitiveMatterSector =
        leftLeptonDoubletTarget
    ; leftLeptonPrimitiveMatterSectorIsLeftLeptonDoublet =
        refl
    ; leftLeptonPrimitiveColourRepresentation =
        canonicalSU3ColourSingletPrimitive
    ; leftLeptonPrimitiveColourRepresentationIsSU3Singlet =
        refl
    ; leftLeptonPrimitiveWeakRepresentation =
        canonicalSU2LWeakDoubletPrimitive
    ; leftLeptonPrimitiveWeakRepresentationIsSU2LDoublet =
        refl
    ; leftLeptonPrimitiveHypercharge =
        canonicalHyperchargeMinusOneHalfPrimitive
    ; leftLeptonPrimitiveHyperchargeIsMinusOneHalf =
        refl
    ; leftLeptonPrimitiveChirality =
        leftChirality
    ; leftLeptonPrimitiveChiralityIsLeft =
        refl
    ; leftLeptonPrimitiveComponents =
        canonicalLeftLeptonTwoWeakComponentPrimitive
    ; leftLeptonPrimitiveComponentsAreTwoWeak =
        refl
    ; leftLeptonPrimitiveGenerations =
        canonicalThreeGenerationPrimitive
    ; leftLeptonPrimitiveGenerationsAreThree =
        refl
    }

record RightChargedLeptonFamilyPrimitive : Set where
  constructor rightChargedLeptonFamilyPrimitive
  field
    rightChargedLeptonPrimitiveMatterSector :
      StandardModelMatterSectorTarget

    rightChargedLeptonPrimitiveMatterSectorIsRightChargedLepton :
      rightChargedLeptonPrimitiveMatterSector
      ≡
      rightChargedLeptonTarget

    rightChargedLeptonPrimitiveColourRepresentation :
      GaugeRepresentationPrimitive

    rightChargedLeptonPrimitiveColourRepresentationIsSU3Singlet :
      rightChargedLeptonPrimitiveColourRepresentation
      ≡
      canonicalSU3ColourSingletPrimitive

    rightChargedLeptonPrimitiveWeakRepresentation :
      GaugeRepresentationPrimitive

    rightChargedLeptonPrimitiveWeakRepresentationIsSU2LSinglet :
      rightChargedLeptonPrimitiveWeakRepresentation
      ≡
      canonicalSU2LWeakSingletPrimitive

    rightChargedLeptonPrimitiveHypercharge :
      HyperchargePrimitive

    rightChargedLeptonPrimitiveHyperchargeIsMinusOne :
      rightChargedLeptonPrimitiveHypercharge
      ≡
      canonicalHyperchargeMinusOnePrimitive

    rightChargedLeptonPrimitiveChirality :
      ChiralityPrimitive

    rightChargedLeptonPrimitiveChiralityIsRight :
      rightChargedLeptonPrimitiveChirality
      ≡
      rightChirality

    rightChargedLeptonPrimitiveComponents :
      ComponentPrimitive

    rightChargedLeptonPrimitiveComponentsAreOne :
      rightChargedLeptonPrimitiveComponents
      ≡
      canonicalRightLeptonOneComponentPrimitive

    rightChargedLeptonPrimitiveGenerations :
      GenerationPrimitive

    rightChargedLeptonPrimitiveGenerationsAreThree :
      rightChargedLeptonPrimitiveGenerations
      ≡
      canonicalThreeGenerationPrimitive

open RightChargedLeptonFamilyPrimitive public

canonicalRightChargedLeptonFamilyPrimitive :
  RightChargedLeptonFamilyPrimitive
canonicalRightChargedLeptonFamilyPrimitive =
  record
    { rightChargedLeptonPrimitiveMatterSector =
        rightChargedLeptonTarget
    ; rightChargedLeptonPrimitiveMatterSectorIsRightChargedLepton =
        refl
    ; rightChargedLeptonPrimitiveColourRepresentation =
        canonicalSU3ColourSingletPrimitive
    ; rightChargedLeptonPrimitiveColourRepresentationIsSU3Singlet =
        refl
    ; rightChargedLeptonPrimitiveWeakRepresentation =
        canonicalSU2LWeakSingletPrimitive
    ; rightChargedLeptonPrimitiveWeakRepresentationIsSU2LSinglet =
        refl
    ; rightChargedLeptonPrimitiveHypercharge =
        canonicalHyperchargeMinusOnePrimitive
    ; rightChargedLeptonPrimitiveHyperchargeIsMinusOne =
        refl
    ; rightChargedLeptonPrimitiveChirality =
        rightChirality
    ; rightChargedLeptonPrimitiveChiralityIsRight =
        refl
    ; rightChargedLeptonPrimitiveComponents =
        canonicalRightLeptonOneComponentPrimitive
    ; rightChargedLeptonPrimitiveComponentsAreOne =
        refl
    ; rightChargedLeptonPrimitiveGenerations =
        canonicalThreeGenerationPrimitive
    ; rightChargedLeptonPrimitiveGenerationsAreThree =
        refl
    }

data HyperchargeAnomalyConditionLabel : Set where
  su3SquaredU1YAnomalyCancellation :
    HyperchargeAnomalyConditionLabel

  su2SquaredU1YAnomalyCancellation :
    HyperchargeAnomalyConditionLabel

  u1YCubedAnomalyCancellation :
    HyperchargeAnomalyConditionLabel

  gravitationalSquaredU1YAnomalyCancellation :
    HyperchargeAnomalyConditionLabel

  globalSU2WittenAnomalyEvenDoublets :
    HyperchargeAnomalyConditionLabel

canonicalHyperchargeAnomalyConditionLabels :
  List HyperchargeAnomalyConditionLabel
canonicalHyperchargeAnomalyConditionLabels =
  su3SquaredU1YAnomalyCancellation
  ∷ su2SquaredU1YAnomalyCancellation
  ∷ u1YCubedAnomalyCancellation
  ∷ gravitationalSquaredU1YAnomalyCancellation
  ∷ globalSU2WittenAnomalyEvenDoublets
  ∷ []

data MatterAdapterBoundary : Set where
  missingCompactGroupGlobalForm :
    MatterAdapterBoundary

  missingRepresentationCategory :
    MatterAdapterBoundary

  missingHyperchargeNormalization :
    MatterAdapterBoundary

  missingAnomalyCancellationProof :
    MatterAdapterBoundary

  missingThreeGenerationDerivation :
    MatterAdapterBoundary

  missingYukawaMatrixDerivation :
    MatterAdapterBoundary

  missingCKMMixingDerivation :
    MatterAdapterBoundary

  missingPMNSMixingDerivation :
    MatterAdapterBoundary

  missingNeutrinoMassAdapter :
    MatterAdapterBoundary

  missingAbsoluteHiggsVEVAndFermionScaleAdapter4 :
    MatterAdapterBoundary

canonicalMatterAdapterBoundaries :
  List MatterAdapterBoundary
canonicalMatterAdapterBoundaries =
  missingCompactGroupGlobalForm
  ∷ missingRepresentationCategory
  ∷ missingHyperchargeNormalization
  ∷ missingAnomalyCancellationProof
  ∷ missingThreeGenerationDerivation
  ∷ missingYukawaMatrixDerivation
  ∷ missingCKMMixingDerivation
  ∷ missingPMNSMixingDerivation
  ∷ missingNeutrinoMassAdapter
  ∷ missingAbsoluteHiggsVEVAndFermionScaleAdapter4
  ∷ []

data YukawaRatioPromotionTarget : Set where
  ratioFormYukawaEigenvalueHierarchyTarget :
    YukawaRatioPromotionTarget

  georgiJarlskogSU5FortyFiveHiggsTarget :
    YukawaRatioPromotionTarget

  froggattNielsenChargeTextureTarget :
    YukawaRatioPromotionTarget

  ckmWolfensteinCabibboFromFNChargeDifferencesTarget :
    YukawaRatioPromotionTarget

  frobeniusPhaseCPSourceTarget :
    YukawaRatioPromotionTarget

  pmnsDemocraticMajoranaFromP7SU2RTarget :
    YukawaRatioPromotionTarget

  seesawScaleReceiptTarget :
    YukawaRatioPromotionTarget

  adapter4AbsoluteHiggsVEVFermionScaleBoundaryTarget :
    YukawaRatioPromotionTarget

canonicalYukawaRatioPromotionTargets :
  List YukawaRatioPromotionTarget
canonicalYukawaRatioPromotionTargets =
  ratioFormYukawaEigenvalueHierarchyTarget
  ∷ georgiJarlskogSU5FortyFiveHiggsTarget
  ∷ froggattNielsenChargeTextureTarget
  ∷ ckmWolfensteinCabibboFromFNChargeDifferencesTarget
  ∷ frobeniusPhaseCPSourceTarget
  ∷ pmnsDemocraticMajoranaFromP7SU2RTarget
  ∷ seesawScaleReceiptTarget
  ∷ adapter4AbsoluteHiggsVEVFermionScaleBoundaryTarget
  ∷ []

data GeorgiJarlskogRelationLabel : Set where
  su5FortyFiveBottomTauRatioOneTarget :
    GeorgiJarlskogRelationLabel

  su5FortyFiveMuonStrangeClebschThreeTarget :
    GeorgiJarlskogRelationLabel

  su5FortyFiveElectronDownClebschOneThirdTarget :
    GeorgiJarlskogRelationLabel

canonicalGeorgiJarlskogRelationLabels :
  List GeorgiJarlskogRelationLabel
canonicalGeorgiJarlskogRelationLabels =
  su5FortyFiveBottomTauRatioOneTarget
  ∷ su5FortyFiveMuonStrangeClebschThreeTarget
  ∷ su5FortyFiveElectronDownClebschOneThirdTarget
  ∷ []

data FroggattNielsenChargeSlot : Set where
  leftQuarkDoubletFNCharge :
    FroggattNielsenChargeSlot

  rightUpQuarkFNCharge :
    FroggattNielsenChargeSlot

  rightDownQuarkFNCharge :
    FroggattNielsenChargeSlot

  leftLeptonDoubletFNCharge :
    FroggattNielsenChargeSlot

  rightChargedLeptonFNCharge :
    FroggattNielsenChargeSlot

  rightNeutrinoFNCharge :
    FroggattNielsenChargeSlot

  higgsFNCharge :
    FroggattNielsenChargeSlot

canonicalFroggattNielsenChargeSlots :
  List FroggattNielsenChargeSlot
canonicalFroggattNielsenChargeSlots =
  leftQuarkDoubletFNCharge
  ∷ rightUpQuarkFNCharge
  ∷ rightDownQuarkFNCharge
  ∷ leftLeptonDoubletFNCharge
  ∷ rightChargedLeptonFNCharge
  ∷ rightNeutrinoFNCharge
  ∷ higgsFNCharge
  ∷ []

data CKMWolfensteinFNRelationLabel : Set where
  cabibboAngleFromLeftQuarkFNChargeDifference12 :
    CKMWolfensteinFNRelationLabel

  vcbFromLeftQuarkFNChargeDifference23 :
    CKMWolfensteinFNRelationLabel

  vubFromLeftQuarkFNChargeDifference13 :
    CKMWolfensteinFNRelationLabel

  wolfensteinHierarchyFromFNChargeDifferences :
    CKMWolfensteinFNRelationLabel

canonicalCKMWolfensteinFNRelationLabels :
  List CKMWolfensteinFNRelationLabel
canonicalCKMWolfensteinFNRelationLabels =
  cabibboAngleFromLeftQuarkFNChargeDifference12
  ∷ vcbFromLeftQuarkFNChargeDifference23
  ∷ vubFromLeftQuarkFNChargeDifference13
  ∷ wolfensteinHierarchyFromFNChargeDifferences
  ∷ []

data FrobeniusPhaseCPSourceLabel : Set where
  crystallineFrobeniusEigenphaseCPSourceTarget :
    FrobeniusPhaseCPSourceLabel

  orderOneYukawaCoefficientPhaseSocket :
    FrobeniusPhaseCPSourceLabel

canonicalFrobeniusPhaseCPSourceLabels :
  List FrobeniusPhaseCPSourceLabel
canonicalFrobeniusPhaseCPSourceLabels =
  crystallineFrobeniusEigenphaseCPSourceTarget
  ∷ orderOneYukawaCoefficientPhaseSocket
  ∷ []

data PMNSMajoranaP7SU2RTarget : Set where
  p7SU2RRightHandedNeutrinoMajoranaTarget :
    PMNSMajoranaP7SU2RTarget

  democraticMajoranaMatrixTextureTarget :
    PMNSMajoranaP7SU2RTarget

  pmnsLargeMixingFromDemocraticMajoranaTarget :
    PMNSMajoranaP7SU2RTarget

canonicalPMNSMajoranaP7SU2RTargets :
  List PMNSMajoranaP7SU2RTarget
canonicalPMNSMajoranaP7SU2RTargets =
  p7SU2RRightHandedNeutrinoMajoranaTarget
  ∷ democraticMajoranaMatrixTextureTarget
  ∷ pmnsLargeMixingFromDemocraticMajoranaTarget
  ∷ []

data SeesawScaleReceiptLabel : Set where
  p7SU2RBreakingScaleReceiptTarget :
    SeesawScaleReceiptLabel

  rightHandedMajoranaMassScaleReceiptTarget :
    SeesawScaleReceiptLabel

  lightNeutrinoRatioFormSeesawReceiptTarget :
    SeesawScaleReceiptLabel

canonicalSeesawScaleReceiptLabels :
  List SeesawScaleReceiptLabel
canonicalSeesawScaleReceiptLabels =
  p7SU2RBreakingScaleReceiptTarget
  ∷ rightHandedMajoranaMassScaleReceiptTarget
  ∷ lightNeutrinoRatioFormSeesawReceiptTarget
  ∷ []

data CompactGaugeGroup : Set where
  compactGaugeGroupTargetOnly :
    CompactGaugeGroup

data GenerationStructure : Set where
  matterGenerationStructure :
    GenerationPrimitive →
    GenerationStructure

canonicalThreeGenerationStructure :
  GenerationStructure
canonicalThreeGenerationStructure =
  matterGenerationStructure canonicalThreeGenerationPrimitive

data MatterRepresentation : Set where
  higgsDoubletMatterRepresentation :
    HiggsDoubletPrimitive →
    MatterRepresentation

  leftQuarkDoubletFamilyMatterRepresentation :
    LeftQuarkDoubletFamilyPrimitive →
    GenerationStructure →
    MatterRepresentation

  rightUpQuarkFamilyMatterRepresentation :
    RightUpQuarkFamilyPrimitive →
    GenerationStructure →
    MatterRepresentation

  rightDownQuarkFamilyMatterRepresentation :
    RightDownQuarkFamilyPrimitive →
    GenerationStructure →
    MatterRepresentation

  leftLeptonDoubletFamilyMatterRepresentation :
    LeftLeptonDoubletFamilyPrimitive →
    GenerationStructure →
    MatterRepresentation

  rightChargedLeptonFamilyMatterRepresentation :
    RightChargedLeptonFamilyPrimitive →
    GenerationStructure →
    MatterRepresentation

  adapterMatterRepresentation :
    CompactGaugeGroup →
    StandardModelMatterSectorTarget →
    MatterRepresentation

canonicalHiggsDoubletMatterRepresentation :
  MatterRepresentation
canonicalHiggsDoubletMatterRepresentation =
  higgsDoubletMatterRepresentation canonicalHiggsDoubletPrimitive

canonicalLeftQuarkDoubletFamilyMatterRepresentation :
  MatterRepresentation
canonicalLeftQuarkDoubletFamilyMatterRepresentation =
  leftQuarkDoubletFamilyMatterRepresentation
    canonicalLeftQuarkDoubletFamilyPrimitive
    canonicalThreeGenerationStructure

canonicalRightUpQuarkFamilyMatterRepresentation :
  MatterRepresentation
canonicalRightUpQuarkFamilyMatterRepresentation =
  rightUpQuarkFamilyMatterRepresentation
    canonicalRightUpQuarkFamilyPrimitive
    canonicalThreeGenerationStructure

canonicalRightDownQuarkFamilyMatterRepresentation :
  MatterRepresentation
canonicalRightDownQuarkFamilyMatterRepresentation =
  rightDownQuarkFamilyMatterRepresentation
    canonicalRightDownQuarkFamilyPrimitive
    canonicalThreeGenerationStructure

canonicalLeftLeptonDoubletFamilyMatterRepresentation :
  MatterRepresentation
canonicalLeftLeptonDoubletFamilyMatterRepresentation =
  leftLeptonDoubletFamilyMatterRepresentation
    canonicalLeftLeptonDoubletFamilyPrimitive
    canonicalThreeGenerationStructure

canonicalRightChargedLeptonFamilyMatterRepresentation :
  MatterRepresentation
canonicalRightChargedLeptonFamilyMatterRepresentation =
  rightChargedLeptonFamilyMatterRepresentation
    canonicalRightChargedLeptonFamilyPrimitive
    canonicalThreeGenerationStructure

matterRepresentationAdapterTarget :
  CompactGaugeGroup →
  StandardModelMatterSectorTarget →
  MatterRepresentation
matterRepresentationAdapterTarget =
  adapterMatterRepresentation

data SMParticle : Set where
  smLeftQuarkDoublet :
    SMParticle

  smRightUpQuark :
    SMParticle

  smRightDownQuark :
    SMParticle

  smLeftLeptonDoublet :
    SMParticle

  smRightChargedLepton :
    SMParticle

  smRightNeutrino :
    SMParticle

  smHiggsDoublet :
    SMParticle

canonicalSMParticles :
  List SMParticle
canonicalSMParticles =
  smLeftQuarkDoublet
  ∷ smRightUpQuark
  ∷ smRightDownQuark
  ∷ smLeftLeptonDoublet
  ∷ smRightChargedLepton
  ∷ smRightNeutrino
  ∷ smHiggsDoublet
  ∷ []

data SMRepresentationSectorSlot : Set where
  canonicalMatterSectorSlot :
    StandardModelMatterSectorTarget →
    SMRepresentationSectorSlot

  rightNeutrinoSectorStagedNoCanonicalSector :
    SMRepresentationSectorSlot

data SMRepresentationRowStatus : Set where
  canonicalLocalRow :
    SMRepresentationRowStatus

  stagedRightNeutrinoRowBlocked :
    SMRepresentationRowStatus

canonicalHyperchargeZeroPrimitive :
  HyperchargePrimitive
canonicalHyperchargeZeroPrimitive =
  record
    { hyperchargeNumerator =
        0
    ; hyperchargeDenominator =
        1
    ; hyperchargePositive =
        true
    ; hyperchargeLabel =
        "Y=0"
    }

canonicalRightNeutrinoOneComponentPrimitive :
  ComponentPrimitive
canonicalRightNeutrinoOneComponentPrimitive =
  record
    { componentCount =
        1
    ; componentLabel =
        "one sterile right neutrino component per generation"
    }

record SMRepresentationTableRow : Set where
  field
    smParticle :
      SMParticle

    sectorSlot :
      SMRepresentationSectorSlot

    colourRepresentation :
      GaugeRepresentationPrimitive

    weakRepresentation :
      GaugeRepresentationPrimitive

    hypercharge :
      HyperchargePrimitive

    chirality :
      ChiralityPrimitive

    components :
      ComponentPrimitive

    generations :
      GenerationPrimitive

    rowStatus :
      SMRepresentationRowStatus

    rowLabel :
      String

open SMRepresentationTableRow public

canonicalLeftQuarkDoubletSMRepresentationTableRow :
  SMRepresentationTableRow
canonicalLeftQuarkDoubletSMRepresentationTableRow =
  record
    { smParticle =
        smLeftQuarkDoublet
    ; sectorSlot =
        canonicalMatterSectorSlot leftQuarkDoubletTarget
    ; colourRepresentation =
        canonicalSU3ColourTripletPrimitive
    ; weakRepresentation =
        canonicalSU2LWeakDoubletPrimitive
    ; hypercharge =
        canonicalHyperchargeOneSixthPrimitive
    ; chirality =
        leftChirality
    ; components =
        canonicalLeftQuarkSixColourWeakComponentPrimitive
    ; generations =
        canonicalThreeGenerationPrimitive
    ; rowStatus =
        canonicalLocalRow
    ; rowLabel =
        "Q_L: (3,2)_{+1/6}"
    }

canonicalRightUpQuarkSMRepresentationTableRow :
  SMRepresentationTableRow
canonicalRightUpQuarkSMRepresentationTableRow =
  record
    { smParticle =
        smRightUpQuark
    ; sectorSlot =
        canonicalMatterSectorSlot rightUpQuarkTarget
    ; colourRepresentation =
        canonicalSU3ColourTripletPrimitive
    ; weakRepresentation =
        canonicalSU2LWeakSingletPrimitive
    ; hypercharge =
        canonicalHyperchargeTwoThirdsPrimitive
    ; chirality =
        rightChirality
    ; components =
        canonicalRightQuarkThreeColourComponentPrimitive
    ; generations =
        canonicalThreeGenerationPrimitive
    ; rowStatus =
        canonicalLocalRow
    ; rowLabel =
        "u_R: (3,1)_{+2/3}"
    }

canonicalRightDownQuarkSMRepresentationTableRow :
  SMRepresentationTableRow
canonicalRightDownQuarkSMRepresentationTableRow =
  record
    { smParticle =
        smRightDownQuark
    ; sectorSlot =
        canonicalMatterSectorSlot rightDownQuarkTarget
    ; colourRepresentation =
        canonicalSU3ColourTripletPrimitive
    ; weakRepresentation =
        canonicalSU2LWeakSingletPrimitive
    ; hypercharge =
        canonicalHyperchargeMinusOneThirdPrimitive
    ; chirality =
        rightChirality
    ; components =
        canonicalRightQuarkThreeColourComponentPrimitive
    ; generations =
        canonicalThreeGenerationPrimitive
    ; rowStatus =
        canonicalLocalRow
    ; rowLabel =
        "d_R: (3,1)_{-1/3}"
    }

canonicalLeftLeptonDoubletSMRepresentationTableRow :
  SMRepresentationTableRow
canonicalLeftLeptonDoubletSMRepresentationTableRow =
  record
    { smParticle =
        smLeftLeptonDoublet
    ; sectorSlot =
        canonicalMatterSectorSlot leftLeptonDoubletTarget
    ; colourRepresentation =
        canonicalSU3ColourSingletPrimitive
    ; weakRepresentation =
        canonicalSU2LWeakDoubletPrimitive
    ; hypercharge =
        canonicalHyperchargeMinusOneHalfPrimitive
    ; chirality =
        leftChirality
    ; components =
        canonicalLeftLeptonTwoWeakComponentPrimitive
    ; generations =
        canonicalThreeGenerationPrimitive
    ; rowStatus =
        canonicalLocalRow
    ; rowLabel =
        "L_L: (1,2)_{-1/2}"
    }

canonicalRightChargedLeptonSMRepresentationTableRow :
  SMRepresentationTableRow
canonicalRightChargedLeptonSMRepresentationTableRow =
  record
    { smParticle =
        smRightChargedLepton
    ; sectorSlot =
        canonicalMatterSectorSlot rightChargedLeptonTarget
    ; colourRepresentation =
        canonicalSU3ColourSingletPrimitive
    ; weakRepresentation =
        canonicalSU2LWeakSingletPrimitive
    ; hypercharge =
        canonicalHyperchargeMinusOnePrimitive
    ; chirality =
        rightChirality
    ; components =
        canonicalRightLeptonOneComponentPrimitive
    ; generations =
        canonicalThreeGenerationPrimitive
    ; rowStatus =
        canonicalLocalRow
    ; rowLabel =
        "e_R: (1,1)_{-1}"
    }

canonicalRightNeutrinoSMRepresentationTableRow :
  SMRepresentationTableRow
canonicalRightNeutrinoSMRepresentationTableRow =
  record
    { smParticle =
        smRightNeutrino
    ; sectorSlot =
        rightNeutrinoSectorStagedNoCanonicalSector
    ; colourRepresentation =
        canonicalSU3ColourSingletPrimitive
    ; weakRepresentation =
        canonicalSU2LWeakSingletPrimitive
    ; hypercharge =
        canonicalHyperchargeZeroPrimitive
    ; chirality =
        rightChirality
    ; components =
        canonicalRightNeutrinoOneComponentPrimitive
    ; generations =
        canonicalThreeGenerationPrimitive
    ; rowStatus =
        stagedRightNeutrinoRowBlocked
    ; rowLabel =
        "nu_R: (1,1)_0 staged; no canonical sector/lane authority"
    }

canonicalHiggsDoubletSMRepresentationTableRow :
  SMRepresentationTableRow
canonicalHiggsDoubletSMRepresentationTableRow =
  record
    { smParticle =
        smHiggsDoublet
    ; sectorSlot =
        canonicalMatterSectorSlot higgsDoubletTarget
    ; colourRepresentation =
        canonicalSU3ColourSingletPrimitive
    ; weakRepresentation =
        canonicalSU2LWeakDoubletPrimitive
    ; hypercharge =
        canonicalHyperchargePlusOnePrimitive
    ; chirality =
        scalarChirality
    ; components =
        canonicalHiggsFourRealComponentPrimitive
    ; generations =
        canonicalThreeGenerationPrimitive
    ; rowStatus =
        canonicalLocalRow
    ; rowLabel =
        "H: (1,2)_{+1}"
    }

canonicalSMRepresentationTableRows :
  List SMRepresentationTableRow
canonicalSMRepresentationTableRows =
  canonicalLeftQuarkDoubletSMRepresentationTableRow
  ∷ canonicalRightUpQuarkSMRepresentationTableRow
  ∷ canonicalRightDownQuarkSMRepresentationTableRow
  ∷ canonicalLeftLeptonDoubletSMRepresentationTableRow
  ∷ canonicalRightChargedLeptonSMRepresentationTableRow
  ∷ canonicalRightNeutrinoSMRepresentationTableRow
  ∷ canonicalHiggsDoubletSMRepresentationTableRow
  ∷ []

record L3SMRepresentationTableReceipt : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    particles :
      List SMParticle

    particlesAreCanonicalSeven :
      particles ≡ canonicalSMParticles

    representationRows :
      List SMRepresentationTableRow

    representationRowsAreCanonicalSeven :
      representationRows ≡ canonicalSMRepresentationTableRows

    rowCount :
      Nat

    rowCountIsSeven :
      rowCount ≡ 7

    sixRowsBackedByExistingMatterRepresentationConstructors :
      Bool

    sixRowsBackedByExistingMatterRepresentationConstructorsIsTrue :
      sixRowsBackedByExistingMatterRepresentationConstructors ≡ true

    rightNeutrinoRowStaged :
      Bool

    rightNeutrinoRowStagedIsTrue :
      rightNeutrinoRowStaged ≡ true

    rightNeutrinoCanonicalSectorAvailable :
      Bool

    rightNeutrinoCanonicalSectorAvailableIsFalse :
      rightNeutrinoCanonicalSectorAvailable ≡ false

    exactSMRepresentationTablePromoted :
      Bool

    exactSMRepresentationTablePromotedIsFalse :
      exactSMRepresentationTablePromoted ≡ false

    noPromotionWithoutAuthority :
      MatterRepresentationPromotionAuthorityToken →
      ⊥

    boundary :
      List String

open L3SMRepresentationTableReceipt public

canonicalL3SMRepresentationTableReceipt :
  L3SMRepresentationTableReceipt
canonicalL3SMRepresentationTableReceipt =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; particles =
        canonicalSMParticles
    ; particlesAreCanonicalSeven =
        refl
    ; representationRows =
        canonicalSMRepresentationTableRows
    ; representationRowsAreCanonicalSeven =
        refl
    ; rowCount =
        7
    ; rowCountIsSeven =
        refl
    ; sixRowsBackedByExistingMatterRepresentationConstructors =
        true
    ; sixRowsBackedByExistingMatterRepresentationConstructorsIsTrue =
        refl
    ; rightNeutrinoRowStaged =
        true
    ; rightNeutrinoRowStagedIsTrue =
        refl
    ; rightNeutrinoCanonicalSectorAvailable =
        false
    ; rightNeutrinoCanonicalSectorAvailableIsFalse =
        refl
    ; exactSMRepresentationTablePromoted =
        false
    ; exactSMRepresentationTablePromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "L3 SM representation table records seven multiplet rows: Q_L, u_R, d_R, L_L, e_R, nu_R, and H"
        ∷ "Six rows are backed by the existing local MatterRepresentation constructors and canonical sector targets"
        ∷ "The right-neutrino row is staged as (1,1)_0 with three generations but has no canonical StandardModelMatterSectorTarget in this surface"
        ∷ "The row therefore records the exact blocker: right-neutrino sector/lane authority remains open"
        ∷ "This is representation-table receipt data, not a Standard Model derivation or promotion"
        ∷ []
    }

record MixingSignedRationalDatum : Set where
  constructor mixingSignedRationalDatum
  field
    numerator :
      Nat

    denominator :
      Nat

    nonnegative :
      Bool

open MixingSignedRationalDatum public

record MixingGaussianRationalDatum : Set where
  constructor mixingGaussianRationalDatum
  field
    realPart :
      MixingSignedRationalDatum

    imaginaryPart :
      MixingSignedRationalDatum

open MixingGaussianRationalDatum public

zeroMixingSignedRationalDatum : MixingSignedRationalDatum
zeroMixingSignedRationalDatum =
  mixingSignedRationalDatum 0 1 true

oneMixingSignedRationalDatum : MixingSignedRationalDatum
oneMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 1 true

minusOneMixingSignedRationalDatum : MixingSignedRationalDatum
minusOneMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 1 false

oneFifthMixingSignedRationalDatum : MixingSignedRationalDatum
oneFifthMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 5 true

minusOneFifthMixingSignedRationalDatum : MixingSignedRationalDatum
minusOneFifthMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 5 false

oneTwentyFifthMixingSignedRationalDatum : MixingSignedRationalDatum
oneTwentyFifthMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 25 true

minusOneTwentyFifthMixingSignedRationalDatum : MixingSignedRationalDatum
minusOneTwentyFifthMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 25 false

fortyNineFiftiethsMixingSignedRationalDatum : MixingSignedRationalDatum
fortyNineFiftiethsMixingSignedRationalDatum =
  mixingSignedRationalDatum 49 50 true

oneFiveHundredMixingSignedRationalDatum : MixingSignedRationalDatum
oneFiveHundredMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 500 true

threeFiveHundredMixingSignedRationalDatum : MixingSignedRationalDatum
threeFiveHundredMixingSignedRationalDatum =
  mixingSignedRationalDatum 3 500 true

minusOneThreeSeventyFiveMixingSignedRationalDatum :
  MixingSignedRationalDatum
minusOneThreeSeventyFiveMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 375 false

thirtySevenNinetyThousandMixingSignedRationalDatum :
  MixingSignedRationalDatum
thirtySevenNinetyThousandMixingSignedRationalDatum =
  mixingSignedRationalDatum 37 90000 true

oneTwelveFiveHundredMixingSignedRationalDatum :
  MixingSignedRationalDatum
oneTwelveFiveHundredMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 12500 true

minusOneTwelveFiveHundredMixingSignedRationalDatum :
  MixingSignedRationalDatum
minusOneTwelveFiveHundredMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 12500 false

oneNineThreeSeventyFiveMixingSignedRationalDatum :
  MixingSignedRationalDatum
oneNineThreeSeventyFiveMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 9375 true

minusOneNineThreeSeventyFiveMixingSignedRationalDatum :
  MixingSignedRationalDatum
minusOneNineThreeSeventyFiveMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 9375 false

threeTwentyFiveThousandMixingSignedRationalDatum :
  MixingSignedRationalDatum
threeTwentyFiveThousandMixingSignedRationalDatum =
  mixingSignedRationalDatum 3 25000 true

minusThreeTwentyFiveThousandMixingSignedRationalDatum :
  MixingSignedRationalDatum
minusThreeTwentyFiveThousandMixingSignedRationalDatum =
  mixingSignedRationalDatum 3 25000 false

oneEighteenSevenFiftyMixingSignedRationalDatum :
  MixingSignedRationalDatum
oneEighteenSevenFiftyMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 18750 true

minusOneEighteenSevenFiftyMixingSignedRationalDatum :
  MixingSignedRationalDatum
minusOneEighteenSevenFiftyMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 18750 false

oneFiveHundredResidualMixingSignedRationalDatum :
  MixingSignedRationalDatum
oneFiveHundredResidualMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 500 true

minusOneTwentyFiveHundredMixingSignedRationalDatum :
  MixingSignedRationalDatum
minusOneTwentyFiveHundredMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 2500 false

oneEighteenSeventyFiveMixingSignedRationalDatum :
  MixingSignedRationalDatum
oneEighteenSeventyFiveMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 1875 true

minusOneEighteenSeventyFiveMixingSignedRationalDatum :
  MixingSignedRationalDatum
minusOneEighteenSeventyFiveMixingSignedRationalDatum =
  mixingSignedRationalDatum 1 1875 false

threeSixNineSevenOverTwoTwoFiveZeroZeroZeroZeroMixingSignedRationalDatum :
  MixingSignedRationalDatum
threeSixNineSevenOverTwoTwoFiveZeroZeroZeroZeroMixingSignedRationalDatum =
  mixingSignedRationalDatum 3697 2250000 true

nineZeroZeroThreeSevenOverNinetyThousandMixingSignedRationalDatum :
  MixingSignedRationalDatum
nineZeroZeroThreeSevenOverNinetyThousandMixingSignedRationalDatum =
  mixingSignedRationalDatum 90037 90000 true

fiveZeroOneOverFiveHundredMixingSignedRationalDatum :
  MixingSignedRationalDatum
fiveZeroOneOverFiveHundredMixingSignedRationalDatum =
  mixingSignedRationalDatum 501 500 true

twoTwoFiveThreeSixNineSevenOverTwoTwoFiveZeroZeroZeroZeroMixingSignedRationalDatum :
  MixingSignedRationalDatum
twoTwoFiveThreeSixNineSevenOverTwoTwoFiveZeroZeroZeroZeroMixingSignedRationalDatum =
  mixingSignedRationalDatum 2253697 2250000 true

zeroMixingGaussianRationalDatum : MixingGaussianRationalDatum
zeroMixingGaussianRationalDatum =
  mixingGaussianRationalDatum
    zeroMixingSignedRationalDatum
    zeroMixingSignedRationalDatum

oneMixingGaussianRationalDatum : MixingGaussianRationalDatum
oneMixingGaussianRationalDatum =
  mixingGaussianRationalDatum
    oneMixingSignedRationalDatum
    zeroMixingSignedRationalDatum

vubWolfensteinMixingGaussianDatum : MixingGaussianRationalDatum
vubWolfensteinMixingGaussianDatum =
  mixingGaussianRationalDatum
    oneFiveHundredMixingSignedRationalDatum
    minusOneThreeSeventyFiveMixingSignedRationalDatum

vtdWolfensteinMixingGaussianDatum : MixingGaussianRationalDatum
vtdWolfensteinMixingGaussianDatum =
  mixingGaussianRationalDatum
    threeFiveHundredMixingSignedRationalDatum
    minusOneThreeSeventyFiveMixingSignedRationalDatum

record MixingMatrix : Set where
  constructor mixingMatrix3x3
  field
    v11 v12 v13 :
      MixingGaussianRationalDatum

    v21 v22 v23 :
      MixingGaussianRationalDatum

    v31 v32 v33 :
      MixingGaussianRationalDatum

open MixingMatrix public

identityMixingMatrix : MixingMatrix
identityMixingMatrix =
  mixingMatrix3x3
    oneMixingGaussianRationalDatum zeroMixingGaussianRationalDatum zeroMixingGaussianRationalDatum
    zeroMixingGaussianRationalDatum oneMixingGaussianRationalDatum zeroMixingGaussianRationalDatum
    zeroMixingGaussianRationalDatum zeroMixingGaussianRationalDatum oneMixingGaussianRationalDatum

canonicalWolfensteinMixingMatrix : MixingMatrix
canonicalWolfensteinMixingMatrix =
  mixingMatrix3x3
    (mixingGaussianRationalDatum
      fortyNineFiftiethsMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      oneFifthMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    vubWolfensteinMixingGaussianDatum
    (mixingGaussianRationalDatum
      minusOneFifthMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      fortyNineFiftiethsMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      oneTwentyFifthMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    vtdWolfensteinMixingGaussianDatum
    (mixingGaussianRationalDatum
      minusOneTwentyFifthMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    oneMixingGaussianRationalDatum

canonicalWolfensteinVVdaggerProductMatrix : MixingMatrix
canonicalWolfensteinVVdaggerProductMatrix =
  mixingMatrix3x3
    (mixingGaussianRationalDatum
      nineZeroZeroThreeSevenOverNinetyThousandMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      oneTwelveFiveHundredMixingSignedRationalDatum
      minusOneNineThreeSeventyFiveMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      minusThreeTwentyFiveThousandMixingSignedRationalDatum
      minusOneEighteenSevenFiftyMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      oneTwelveFiveHundredMixingSignedRationalDatum
      oneNineThreeSeventyFiveMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      fiveZeroOneOverFiveHundredMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      minusOneTwentyFiveHundredMixingSignedRationalDatum
      minusOneEighteenSeventyFiveMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      minusThreeTwentyFiveThousandMixingSignedRationalDatum
      oneEighteenSevenFiftyMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      minusOneTwentyFiveHundredMixingSignedRationalDatum
      oneEighteenSeventyFiveMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      twoTwoFiveThreeSixNineSevenOverTwoTwoFiveZeroZeroZeroZeroMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)

canonicalWolfensteinVVdaggerMinusIdentityResidual :
  MixingMatrix
canonicalWolfensteinVVdaggerMinusIdentityResidual =
  mixingMatrix3x3
    (mixingGaussianRationalDatum
      thirtySevenNinetyThousandMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      oneTwelveFiveHundredMixingSignedRationalDatum
      minusOneNineThreeSeventyFiveMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      minusThreeTwentyFiveThousandMixingSignedRationalDatum
      minusOneEighteenSevenFiftyMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      oneTwelveFiveHundredMixingSignedRationalDatum
      oneNineThreeSeventyFiveMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      oneFiveHundredResidualMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      minusOneTwentyFiveHundredMixingSignedRationalDatum
      minusOneEighteenSeventyFiveMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      minusThreeTwentyFiveThousandMixingSignedRationalDatum
      oneEighteenSevenFiftyMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      minusOneTwentyFiveHundredMixingSignedRationalDatum
      oneEighteenSeventyFiveMixingSignedRationalDatum)
    (mixingGaussianRationalDatum
      threeSixNineSevenOverTwoTwoFiveZeroZeroZeroZeroMixingSignedRationalDatum
      zeroMixingSignedRationalDatum)

leftIdentityMixingProduct : MixingMatrix → MixingMatrix
leftIdentityMixingProduct V =
  V

canonicalWolfensteinLeftIdentityProductClosure :
  leftIdentityMixingProduct canonicalWolfensteinMixingMatrix
  ≡
  canonicalWolfensteinMixingMatrix
canonicalWolfensteinLeftIdentityProductClosure =
  refl

data HyperchargeAssignment : Set where
  hyperchargeAssignmentTargetOnly :
    StandardModelMatterSectorTarget →
    HyperchargeAssignment

data AnomalyClass : Set where
  anomalyClassTargetOnly :
    HyperchargeAssignment →
    AnomalyClass

data YukawaSector : Set where
  yukawaSectorTargetOnly :
    YukawaSector

data NeutrinoSector : Set where
  neutrinoSectorTargetOnly :
    NeutrinoSector

hyperchargeAssignmentTarget :
  StandardModelMatterSectorTarget →
  HyperchargeAssignment
hyperchargeAssignmentTarget =
  hyperchargeAssignmentTargetOnly

anomalyClassTarget :
  HyperchargeAssignment →
  AnomalyClass
anomalyClassTarget =
  anomalyClassTargetOnly

data AbstractMatterPrimeLaneDHREndoTarget
  (p : Moonshine.MonsterPrimeLane)
  (ρ : DHR.LocalisedEndomorphism) :
  Set where
  matterPrimeLaneDHREndoTargetOnly :
    AbstractMatterPrimeLaneDHREndoTarget p ρ

abstractMatterPrimeLaneDHREndoTarget :
  Moonshine.MonsterPrimeLane →
  DHR.LocalisedEndomorphism →
  Set
abstractMatterPrimeLaneDHREndoTarget p ρ =
  AbstractMatterPrimeLaneDHREndoTarget p ρ

data AbstractMatterPrimeLaneTransportTarget
  (p : Moonshine.MonsterPrimeLane)
  (ρ : DHR.LocalisedEndomorphism)
  (transportable : DHR.Transportable ρ) :
  Set where
  matterPrimeLaneTransportTargetOnly :
    AbstractMatterPrimeLaneTransportTarget p ρ transportable

abstractMatterPrimeLaneTransportTarget :
  (p : Moonshine.MonsterPrimeLane) →
  (ρ : DHR.LocalisedEndomorphism) →
  DHR.Transportable ρ →
  Set
abstractMatterPrimeLaneTransportTarget p ρ transportable =
  AbstractMatterPrimeLaneTransportTarget p ρ transportable

data AbstractMatterPrimeLaneSectorTarget
  (p : Moonshine.MonsterPrimeLane)
  (sector : StandardModelMatterSectorTarget)
  (representation : MatterRepresentation) :
  Set where
  matterPrimeLaneSectorTargetOnly :
    AbstractMatterPrimeLaneSectorTarget p sector representation

abstractMatterPrimeLaneSectorTarget :
  Moonshine.MonsterPrimeLane →
  StandardModelMatterSectorTarget →
  MatterRepresentation →
  Set
abstractMatterPrimeLaneSectorTarget p sector representation =
  AbstractMatterPrimeLaneSectorTarget p sector representation

data SerreTateDefSpaceAtPrimeLane
  (p : Moonshine.MonsterPrimeLane) :
  Set where
  serreTateDefSpaceTargetOnly :
    SerreTateDefSpaceAtPrimeLane p

data HiggsFNChargeAdapter : Set where
  higgsFNChargeAdapterTargetOnly :
    HiggsFNChargeAdapter

data YukawaTextureTarget : Set where
  yukawaTextureTargetOnly :
    YukawaTextureTarget

data FrobeniusPhaseReceipt : Set where
  frobeniusPhaseReceiptTargetOnly :
    FrobeniusPhaseReceipt

data CKMCPConditionalTarget : Set where
  ckmCPConditionalTargetOnly :
    CKMCPConditionalTarget

matterPrimeLaneYukawaTextureTarget :
  (p : Moonshine.MonsterPrimeLane) →
  FractranLane.MonsterPrimeLaneAtLeast11 p →
  SerreTateDefSpaceAtPrimeLane p →
  HiggsFNChargeAdapter →
  YukawaTextureTarget
matterPrimeLaneYukawaTextureTarget _ _ _ _ =
  yukawaTextureTargetOnly

ckmCPFromFrobeniusConditionalTarget :
  FrobeniusPhaseReceipt →
  CKMCPConditionalTarget
ckmCPFromFrobeniusConditionalTarget _ =
  ckmCPConditionalTargetOnly

data Tranche2MatterOpenObligation : Set where
  listedMatterLaneCountElevenOpen :
    Tranche2MatterOpenObligation

  missingSerreTateDefSpaceForEachMatterLane :
    Tranche2MatterOpenObligation

  thirdGenerationOnlyThreePrimeLanesOpen :
    Tranche2MatterOpenObligation

  missingOrAmbiguousRightNeutrinoLane :
    Tranche2MatterOpenObligation

  missingHiggsFNChargeNormalisationAdapter :
    Tranche2MatterOpenObligation

  topYukawaHiggsChargeNormalisationInconsistent :
    Tranche2MatterOpenObligation

  missingExactFNYukawaTextureProof :
    Tranche2MatterOpenObligation

  missingFrobeniusPhaseToCKMCPNumerics :
    Tranche2MatterOpenObligation

  absoluteHiggsVEVRemainsAdapter4 :
    Tranche2MatterOpenObligation

canonicalTranche2MatterOpenObligations :
  List Tranche2MatterOpenObligation
canonicalTranche2MatterOpenObligations =
  listedMatterLaneCountElevenOpen
  ∷ missingSerreTateDefSpaceForEachMatterLane
  ∷ thirdGenerationOnlyThreePrimeLanesOpen
  ∷ missingOrAmbiguousRightNeutrinoLane
  ∷ missingHiggsFNChargeNormalisationAdapter
  ∷ topYukawaHiggsChargeNormalisationInconsistent
  ∷ missingExactFNYukawaTextureProof
  ∷ missingFrobeniusPhaseToCKMCPNumerics
  ∷ absoluteHiggsVEVRemainsAdapter4
  ∷ []

data PatiSalamMatterRepresentationTarget : Set where
  leftGenerationFourTwoOneTarget :
    PatiSalamMatterRepresentationTarget

  rightGenerationBarFourOneTwoTarget :
    PatiSalamMatterRepresentationTarget

  psFourBranchesToColourTripletBMinusLThirdTarget :
    PatiSalamMatterRepresentationTarget

  psFourBranchesToLeptonSingletBMinusLOneTarget :
    PatiSalamMatterRepresentationTarget

  threeGenerationGroupingTarget :
    PatiSalamMatterRepresentationTarget

  firstGenerationMatterPrimeGroupTarget :
    PatiSalamMatterRepresentationTarget

  secondGenerationMatterPrimeGroupTarget :
    PatiSalamMatterRepresentationTarget

  thirdGenerationMatterPrimeGroupIncompleteTarget :
    PatiSalamMatterRepresentationTarget

  rightNeutrinoLaneAmbiguityTarget :
    PatiSalamMatterRepresentationTarget

canonicalPatiSalamMatterRepresentationTargets :
  List PatiSalamMatterRepresentationTarget
canonicalPatiSalamMatterRepresentationTargets =
  leftGenerationFourTwoOneTarget
  ∷ rightGenerationBarFourOneTwoTarget
  ∷ psFourBranchesToColourTripletBMinusLThirdTarget
  ∷ psFourBranchesToLeptonSingletBMinusLOneTarget
  ∷ threeGenerationGroupingTarget
  ∷ firstGenerationMatterPrimeGroupTarget
  ∷ secondGenerationMatterPrimeGroupTarget
  ∷ thirdGenerationMatterPrimeGroupIncompleteTarget
  ∷ rightNeutrinoLaneAmbiguityTarget
  ∷ []

proposedFirstGenerationMatterPrimeLanes :
  List Moonshine.MonsterPrimeLane
proposedFirstGenerationMatterPrimeLanes =
  Moonshine.p11
  ∷ Moonshine.p13
  ∷ Moonshine.p17
  ∷ Moonshine.p19
  ∷ []

proposedSecondGenerationMatterPrimeLanes :
  List Moonshine.MonsterPrimeLane
proposedSecondGenerationMatterPrimeLanes =
  Moonshine.p23
  ∷ Moonshine.p29
  ∷ Moonshine.p31
  ∷ Moonshine.p41
  ∷ []

proposedThirdGenerationMatterPrimeLanesIncomplete :
  List Moonshine.MonsterPrimeLane
proposedThirdGenerationMatterPrimeLanesIncomplete =
  Moonshine.p47
  ∷ Moonshine.p59
  ∷ Moonshine.p71
  ∷ []

record Tranche2MatterLaneInventoryReceipt : Setω where
  field
    gaugeLanes :
      List Moonshine.MonsterPrimeLane

    gaugeLanesAreCanonical :
      gaugeLanes
      ≡
      FractranLane.canonicalPatiSalamGaugePrimeLanes

    nonGaugeMatterLanes :
      List Moonshine.MonsterPrimeLane

    nonGaugeMatterLanesAreCanonical :
      nonGaugeMatterLanes
      ≡
      FractranLane.canonicalNonGaugeMatterPrimeLanesAfterPatiSalamGauge

    matterLaneCardinalityMismatch :
      FractranLane.MatterLaneCardinalityMismatch

    mismatchInputTwelveCount :
      Nat

    mismatchInputTwelveCountIsFractranLegacyExpected :
      mismatchInputTwelveCount
      ≡
      FractranLane.expectedMatterLaneCountAfterFourGaugeLanes

    actualMatterLaneCount :
      Nat

    actualMatterLaneCountIs11 :
      actualMatterLaneCount
      ≡
      FractranLane.actualMatterLaneCountAfterFourGaugeLanes

    listedMatterLanesAreElevenNotTwelve :
      Bool

    listedMatterLanesAreElevenNotTwelveIsTrue :
      listedMatterLanesAreElevenNotTwelve ≡ true

    mismatchBlocksMatterPromotion :
      Bool

    mismatchBlocksMatterPromotionIsTrue :
      mismatchBlocksMatterPromotion ≡ true

    boundary :
      List String

open Tranche2MatterLaneInventoryReceipt public

canonicalTranche2MatterLaneInventoryReceipt :
  Tranche2MatterLaneInventoryReceipt
canonicalTranche2MatterLaneInventoryReceipt =
  record
    { gaugeLanes =
        FractranLane.canonicalPatiSalamGaugePrimeLanes
    ; gaugeLanesAreCanonical =
        refl
    ; nonGaugeMatterLanes =
        FractranLane.canonicalNonGaugeMatterPrimeLanesAfterPatiSalamGauge
    ; nonGaugeMatterLanesAreCanonical =
        refl
    ; matterLaneCardinalityMismatch =
        FractranLane.canonicalMatterLaneCardinalityMismatch
    ; mismatchInputTwelveCount =
        FractranLane.expectedMatterLaneCountAfterFourGaugeLanes
    ; mismatchInputTwelveCountIsFractranLegacyExpected =
        refl
    ; actualMatterLaneCount =
        FractranLane.actualMatterLaneCountAfterFourGaugeLanes
    ; actualMatterLaneCountIs11 =
        refl
    ; listedMatterLanesAreElevenNotTwelve =
        true
    ; listedMatterLanesAreElevenNotTwelveIsTrue =
        refl
    ; mismatchBlocksMatterPromotion =
        true
    ; mismatchBlocksMatterPromotionIsTrue =
        refl
    ; boundary =
        "Gauge lanes are {2,3,5,7}; listed matter lanes are {11,13,17,19,23,29,31,41,47,59,71}"
        ∷ "The listed p>=11 matter lane set has 11 entries, not 12"
        ∷ "The retained twelve-count input is only the Fractran mismatch witness, not an instruction to pad the matter lane list"
        ∷ "Matter generation assignment is therefore recorded as open, not silently completed"
        ∷ []
    }

record PatiSalamMatterPerGenerationReceipt : Setω where
  field
    representationTargets :
      List PatiSalamMatterRepresentationTarget

    representationTargetsAreCanonical :
      representationTargets
      ≡
      canonicalPatiSalamMatterRepresentationTargets

    leftMatterRepLabel :
      String

    leftMatterRepLabel-v :
      leftMatterRepLabel
      ≡
      "(4,2,1)"

    rightMatterRepLabel :
      String

    rightMatterRepLabel-v :
      rightMatterRepLabel
      ≡
      "(bar4,1,2)"

    psFourBranchingTarget :
      String

    psFourBranchingTarget-v :
      psFourBranchingTarget
      ≡
      "4 -> 3_{1/3} + 1_{-1}"

    proposedFirstGenerationPrimeGroup :
      List Moonshine.MonsterPrimeLane

    proposedFirstGenerationPrimeGroupIsCanonical :
      proposedFirstGenerationPrimeGroup
      ≡
      proposedFirstGenerationMatterPrimeLanes

    proposedSecondGenerationPrimeGroup :
      List Moonshine.MonsterPrimeLane

    proposedSecondGenerationPrimeGroupIsCanonical :
      proposedSecondGenerationPrimeGroup
      ≡
      proposedSecondGenerationMatterPrimeLanes

    proposedThirdGenerationPrimeGroup :
      List Moonshine.MonsterPrimeLane

    proposedThirdGenerationPrimeGroupIsIncompleteCanonical :
      proposedThirdGenerationPrimeGroup
      ≡
      proposedThirdGenerationMatterPrimeLanesIncomplete

    thirdGenerationOnlyThreePrimes :
      Bool

    thirdGenerationOnlyThreePrimesIsTrue :
      thirdGenerationOnlyThreePrimes ≡ true

    rightNeutrinoLaneMissingOrAmbiguous :
      Bool

    rightNeutrinoLaneMissingOrAmbiguousIsTrue :
      rightNeutrinoLaneMissingOrAmbiguous ≡ true

    threeGenerationGroupingPromoted :
      Bool

    threeGenerationGroupingPromotedIsFalse :
      threeGenerationGroupingPromoted ≡ false

    branchingPromoted :
      Bool

    branchingPromotedIsFalse :
      branchingPromoted ≡ false

    boundary :
      List String

open PatiSalamMatterPerGenerationReceipt public

canonicalPatiSalamMatterPerGenerationReceipt :
  PatiSalamMatterPerGenerationReceipt
canonicalPatiSalamMatterPerGenerationReceipt =
  record
    { representationTargets =
        canonicalPatiSalamMatterRepresentationTargets
    ; representationTargetsAreCanonical =
        refl
    ; leftMatterRepLabel =
        "(4,2,1)"
    ; leftMatterRepLabel-v =
        refl
    ; rightMatterRepLabel =
        "(bar4,1,2)"
    ; rightMatterRepLabel-v =
        refl
    ; psFourBranchingTarget =
        "4 -> 3_{1/3} + 1_{-1}"
    ; psFourBranchingTarget-v =
        refl
    ; proposedFirstGenerationPrimeGroup =
        proposedFirstGenerationMatterPrimeLanes
    ; proposedFirstGenerationPrimeGroupIsCanonical =
        refl
    ; proposedSecondGenerationPrimeGroup =
        proposedSecondGenerationMatterPrimeLanes
    ; proposedSecondGenerationPrimeGroupIsCanonical =
        refl
    ; proposedThirdGenerationPrimeGroup =
        proposedThirdGenerationMatterPrimeLanesIncomplete
    ; proposedThirdGenerationPrimeGroupIsIncompleteCanonical =
        refl
    ; thirdGenerationOnlyThreePrimes =
        true
    ; thirdGenerationOnlyThreePrimesIsTrue =
        refl
    ; rightNeutrinoLaneMissingOrAmbiguous =
        true
    ; rightNeutrinoLaneMissingOrAmbiguousIsTrue =
        refl
    ; threeGenerationGroupingPromoted =
        false
    ; threeGenerationGroupingPromotedIsFalse =
        refl
    ; branchingPromoted =
        false
    ; branchingPromotedIsFalse =
        refl
    ; boundary =
        "Pati-Salam matter target per generation is (4,2,1) plus (bar4,1,2)"
        ∷ "The SU(4) Pati-Salam branching target is 4 -> 3_{1/3} + 1_{-1}"
        ∷ "Proposed matter-prime grouping is generation 1 {11,13,17,19}, generation 2 {23,29,31,41}, generation 3 {47,59,71}"
        ∷ "The third generation grouping is incomplete/open: it has only three primes and leaves a missing or right-neutrino lane ambiguity"
        ∷ "This receipt records representation targets; it does not prove generation assignment from the available matter lanes"
        ∷ []
    }

data RightNeutrinoLaneCandidateStatus : Set where
  stagedRightNeutrinoCandidateFromExistingThirdGeneration :
    RightNeutrinoLaneCandidateStatus

record ThirdGenerationRightNeutrinoCandidateReceipt : Setω where
  field
    priorPerGenerationReceipt :
      PatiSalamMatterPerGenerationReceipt

    priorThirdGenerationOnlyThreePrimesIsTrue :
      thirdGenerationOnlyThreePrimes priorPerGenerationReceipt ≡ true

    priorRightNeutrinoLaneMissingOrAmbiguousIsTrue :
      rightNeutrinoLaneMissingOrAmbiguous priorPerGenerationReceipt ≡ true

    candidateLane :
      Moonshine.MonsterPrimeLane

    candidateLaneIsThirdGenerationPrime :
      candidateLane ≡ Moonshine.p71

    candidateStatus :
      RightNeutrinoLaneCandidateStatus

    candidateStatusIsStaged :
      candidateStatus
      ≡
      stagedRightNeutrinoCandidateFromExistingThirdGeneration

    rightNeutrinoLaneMissingOrAmbiguousStillTrue :
      Bool

    rightNeutrinoLaneMissingOrAmbiguousStillTrueIsTrue :
      rightNeutrinoLaneMissingOrAmbiguousStillTrue ≡ true

    thirdGenerationGroupingPromotedStillFalse :
      Bool

    thirdGenerationGroupingPromotedStillFalseIsFalse :
      thirdGenerationGroupingPromotedStillFalse ≡ false

    candidateBoundary :
      List String

open ThirdGenerationRightNeutrinoCandidateReceipt public

canonicalThirdGenerationRightNeutrinoCandidateReceipt :
  ThirdGenerationRightNeutrinoCandidateReceipt
canonicalThirdGenerationRightNeutrinoCandidateReceipt =
  record
    { priorPerGenerationReceipt =
        canonicalPatiSalamMatterPerGenerationReceipt
    ; priorThirdGenerationOnlyThreePrimesIsTrue =
        refl
    ; priorRightNeutrinoLaneMissingOrAmbiguousIsTrue =
        refl
    ; candidateLane =
        Moonshine.p71
    ; candidateLaneIsThirdGenerationPrime =
        refl
    ; candidateStatus =
        stagedRightNeutrinoCandidateFromExistingThirdGeneration
    ; candidateStatusIsStaged =
        refl
    ; rightNeutrinoLaneMissingOrAmbiguousStillTrue =
        true
    ; rightNeutrinoLaneMissingOrAmbiguousStillTrueIsTrue =
        refl
    ; thirdGenerationGroupingPromotedStillFalse =
        false
    ; thirdGenerationGroupingPromotedStillFalseIsFalse =
        refl
    ; candidateBoundary =
        "A staged right-neutrino candidate lane is now recorded from the existing third-generation set"
        ∷ "The staged candidate is p71, but lane uniqueness and missing-lane authority are still open"
        ∷ "Third-generation grouping therefore remains non-promoted and right-neutrino ambiguity is explicitly preserved"
        ∷ []
    }

rightNeutrinoCandidateReceiptUsesP71 :
  candidateLane canonicalThirdGenerationRightNeutrinoCandidateReceipt
  ≡
  Moonshine.p71
rightNeutrinoCandidateReceiptUsesP71 =
  refl

rightNeutrinoCandidateReceiptKeepsAmbiguityOpen :
  rightNeutrinoLaneMissingOrAmbiguousStillTrue
    canonicalThirdGenerationRightNeutrinoCandidateReceipt
  ≡
  true
rightNeutrinoCandidateReceiptKeepsAmbiguityOpen =
  refl

record MatterPrimeLaneYukawaFNReceipt : Setω where
  field
    laneInventory :
      Tranche2MatterLaneInventoryReceipt

    patiSalamMatterPerGeneration :
      PatiSalamMatterPerGenerationReceipt

    stagedRightNeutrinoCandidate :
      ThirdGenerationRightNeutrinoCandidateReceipt

    stagedRightNeutrinoCandidateKeepsAmbiguityOpen :
      rightNeutrinoLaneMissingOrAmbiguousStillTrue
        stagedRightNeutrinoCandidate
      ≡
      true

    fnChargeFromMonsterValuation :
      FractranLane.FNChargeFromMonsterValuationReceipt

    serreTateDefSpace :
      Moonshine.MonsterPrimeLane →
      Set

    serreTateDefSpaceIsCanonical :
      serreTateDefSpace
      ≡
      SerreTateDefSpaceAtPrimeLane

    higgsFNChargeAdapterCarrier :
      Set

    higgsFNChargeAdapterCarrierIsCanonical :
      higgsFNChargeAdapterCarrier
      ≡
      HiggsFNChargeAdapter

    yukawaTextureCarrier :
      Set

    yukawaTextureCarrierIsCanonical :
      yukawaTextureCarrier
      ≡
      YukawaTextureTarget

    conditionalMatterLaneYukawaTexture :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      serreTateDefSpace p →
      higgsFNChargeAdapterCarrier →
      yukawaTextureCarrier

    ckmCPConditionalCarrier :
      Set

    ckmCPConditionalCarrierIsCanonical :
      ckmCPConditionalCarrier
      ≡
      CKMCPConditionalTarget

    ckmCPConditionalFromFrobenius :
      FrobeniusPhaseReceipt →
      ckmCPConditionalCarrier

    openObligations :
      List Tranche2MatterOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalTranche2MatterOpenObligations

    fnValuationTargetRecorded :
      Bool

    fnValuationTargetRecordedIsTrue :
      fnValuationTargetRecorded ≡ true

    higgsChargeNormalisationAdapter4 :
      Bool

    higgsChargeNormalisationAdapter4IsTrue :
      higgsChargeNormalisationAdapter4 ≡ true

    fnChargeSketch :
      String

    fnChargeSketch-v :
      fnChargeSketch
      ≡
      "q_p = v_p(|M|)-2"

    topYukawaHiggsChargeBoundary :
      String

    topYukawaHiggsChargeBoundary-v :
      topYukawaHiggsChargeBoundary
      ≡
      "top Yukawa wants q_Q3 + q_u3 + q_H = 0, but q_H is not fixed by q_p = v_p(|M|)-2"

    qHRemainsAdapter4NormalisationInput :
      Bool

    qHRemainsAdapter4NormalisationInputIsTrue :
      qHRemainsAdapter4NormalisationInput ≡ true

    topYukawaHiggsChargeInconsistencyOpen :
      Bool

    topYukawaHiggsChargeInconsistencyOpenIsTrue :
      topYukawaHiggsChargeInconsistencyOpen ≡ true

    ckmAndCPRemainConditional :
      Bool

    ckmAndCPRemainConditionalIsTrue :
      ckmAndCPRemainConditional ≡ true

    absoluteHiggsVEVRemainsAdapter4Flag :
      Bool

    absoluteHiggsVEVRemainsAdapter4FlagIsTrue :
      absoluteHiggsVEVRemainsAdapter4Flag ≡ true

    exactTexturePromoted :
      Bool

    exactTexturePromotedIsFalse :
      exactTexturePromoted ≡ false

    matterPrimeLaneReceiptPromoted :
      Bool

    matterPrimeLaneReceiptPromotedIsFalse :
      matterPrimeLaneReceiptPromoted ≡ false

    boundary :
      List String

open MatterPrimeLaneYukawaFNReceipt public

canonicalMatterPrimeLaneYukawaFNReceipt :
  MatterPrimeLaneYukawaFNReceipt
canonicalMatterPrimeLaneYukawaFNReceipt =
  record
    { laneInventory =
        canonicalTranche2MatterLaneInventoryReceipt
    ; patiSalamMatterPerGeneration =
        canonicalPatiSalamMatterPerGenerationReceipt
    ; stagedRightNeutrinoCandidate =
        canonicalThirdGenerationRightNeutrinoCandidateReceipt
    ; stagedRightNeutrinoCandidateKeepsAmbiguityOpen =
        refl
    ; fnChargeFromMonsterValuation =
        FractranLane.canonicalFNChargeFromMonsterValuationReceipt
    ; serreTateDefSpace =
        SerreTateDefSpaceAtPrimeLane
    ; serreTateDefSpaceIsCanonical =
        refl
    ; higgsFNChargeAdapterCarrier =
        HiggsFNChargeAdapter
    ; higgsFNChargeAdapterCarrierIsCanonical =
        refl
    ; yukawaTextureCarrier =
        YukawaTextureTarget
    ; yukawaTextureCarrierIsCanonical =
        refl
    ; conditionalMatterLaneYukawaTexture =
        matterPrimeLaneYukawaTextureTarget
    ; ckmCPConditionalCarrier =
        CKMCPConditionalTarget
    ; ckmCPConditionalCarrierIsCanonical =
        refl
    ; ckmCPConditionalFromFrobenius =
        ckmCPFromFrobeniusConditionalTarget
    ; openObligations =
        canonicalTranche2MatterOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; fnValuationTargetRecorded =
        true
    ; fnValuationTargetRecordedIsTrue =
        refl
    ; higgsChargeNormalisationAdapter4 =
        true
    ; higgsChargeNormalisationAdapter4IsTrue =
        refl
    ; fnChargeSketch =
        "q_p = v_p(|M|)-2"
    ; fnChargeSketch-v =
        refl
    ; topYukawaHiggsChargeBoundary =
        "top Yukawa wants q_Q3 + q_u3 + q_H = 0, but q_H is not fixed by q_p = v_p(|M|)-2"
    ; topYukawaHiggsChargeBoundary-v =
        refl
    ; qHRemainsAdapter4NormalisationInput =
        true
    ; qHRemainsAdapter4NormalisationInputIsTrue =
        refl
    ; topYukawaHiggsChargeInconsistencyOpen =
        true
    ; topYukawaHiggsChargeInconsistencyOpenIsTrue =
        refl
    ; ckmAndCPRemainConditional =
        true
    ; ckmAndCPRemainConditionalIsTrue =
        refl
    ; absoluteHiggsVEVRemainsAdapter4Flag =
        true
    ; absoluteHiggsVEVRemainsAdapter4FlagIsTrue =
        refl
    ; exactTexturePromoted =
        false
    ; exactTexturePromotedIsFalse =
        refl
    ; matterPrimeLaneReceiptPromoted =
        false
    ; matterPrimeLaneReceiptPromotedIsFalse =
        refl
    ; boundary =
        "MatterPrimeLaneReceipt is conditional on Serre-Tate deformation data for p>=11 and a Higgs FN charge adapter q_H"
        ∷ "Pati-Salam per-generation targets are (4,2,1) plus (bar4,1,2), with 4 -> 3_{1/3} + 1_{-1} as a branching target"
        ∷ "FN charge target q_p = v_p(|M|)-2 is recorded: valuation 2 -> 0, valuation 1 -> -1"
        ∷ "Top-Yukawa neutrality exposes a Higgs-charge inconsistency unless q_H is supplied externally"
        ∷ "q_H is therefore an Adapter4 normalisation input, not a derived matter-prime output"
        ∷ "The available post-gauge list contains 11 matter primes, not 12, so the proposed three-generation assignment is an open obligation"
        ∷ "A staged right-neutrino candidate lane p71 is now recorded, but uniqueness and missing-lane authority remain open"
        ∷ "CKM/CP/Frobenius phase and exact Yukawa textures remain conditional; absolute Higgs vev remains Adapter 4"
        ∷ []
    }

record YukawaSectorRatioFormPromotionReceipt : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    ratioPromotionTargets :
      List YukawaRatioPromotionTarget

    ratioPromotionTargetsAreCanonical :
      ratioPromotionTargets
      ≡
      canonicalYukawaRatioPromotionTargets

    georgiJarlskogRelations :
      List GeorgiJarlskogRelationLabel

    georgiJarlskogRelationsAreCanonical :
      georgiJarlskogRelations
      ≡
      canonicalGeorgiJarlskogRelationLabels

    froggattNielsenChargeSlots :
      List FroggattNielsenChargeSlot

    froggattNielsenChargeSlotsAreCanonical :
      froggattNielsenChargeSlots
      ≡
      canonicalFroggattNielsenChargeSlots

    ckmWolfensteinFNRelations :
      List CKMWolfensteinFNRelationLabel

    ckmWolfensteinFNRelationsAreCanonical :
      ckmWolfensteinFNRelations
      ≡
      canonicalCKMWolfensteinFNRelationLabels

    frobeniusPhaseCPSources :
      List FrobeniusPhaseCPSourceLabel

    frobeniusPhaseCPSourcesAreCanonical :
      frobeniusPhaseCPSources
      ≡
      canonicalFrobeniusPhaseCPSourceLabels

    pmnsMajoranaP7SU2RTargets :
      List PMNSMajoranaP7SU2RTarget

    pmnsMajoranaP7SU2RTargetsAreCanonical :
      pmnsMajoranaP7SU2RTargets
      ≡
      canonicalPMNSMajoranaP7SU2RTargets

    seesawScaleReceipts :
      List SeesawScaleReceiptLabel

    seesawScaleReceiptsAreCanonical :
      seesawScaleReceipts
      ≡
      canonicalSeesawScaleReceiptLabels

    p7SeesawLane :
      Moonshine.MonsterPrimeLane

    p7SeesawLaneIsCanonical :
      p7SeesawLane ≡ Moonshine.p7

    p7HighEnergyAssignment :
      FractranLane.HighEnergyPatiSalamLaneAssignment

    p7HighEnergyAssignmentIsSU2RBrokenAtSeesaw :
      p7HighEnergyAssignment
      ≡
      FractranLane.assignedSU2RBrokenAtSeesaw

    ratioFormPromotionTargetRecorded :
      Bool

    ratioFormPromotionTargetRecordedIsTrue :
      ratioFormPromotionTargetRecorded ≡ true

    georgiJarlskogSU5FortyFiveRecorded :
      Bool

    georgiJarlskogSU5FortyFiveRecordedIsTrue :
      georgiJarlskogSU5FortyFiveRecorded ≡ true

    froggattNielsenTextureRecorded :
      Bool

    froggattNielsenTextureRecordedIsTrue :
      froggattNielsenTextureRecorded ≡ true

    ckmWolfensteinCabibboFromFNRecorded :
      Bool

    ckmWolfensteinCabibboFromFNRecordedIsTrue :
      ckmWolfensteinCabibboFromFNRecorded ≡ true

    frobeniusPhaseCPSourceRecorded :
      Bool

    frobeniusPhaseCPSourceRecordedIsTrue :
      frobeniusPhaseCPSourceRecorded ≡ true

    pmnsDemocraticMajoranaP7SU2RRecorded :
      Bool

    pmnsDemocraticMajoranaP7SU2RRecordedIsTrue :
      pmnsDemocraticMajoranaP7SU2RRecorded ≡ true

    seesawScaleReceiptRecorded :
      Bool

    seesawScaleReceiptRecordedIsTrue :
      seesawScaleReceiptRecorded ≡ true

    exactMatrixNumericsPromoted :
      Bool

    exactMatrixNumericsPromotedIsFalse :
      exactMatrixNumericsPromoted ≡ false

    absoluteHiggsVEVOrFermionScaleDerived :
      Bool

    absoluteHiggsVEVOrFermionScaleDerivedIsFalse :
      absoluteHiggsVEVOrFermionScaleDerived ≡ false

    adapter4AbsoluteScaleBoundary :
      String

    ratioPromotionPromoted :
      Bool

    ratioPromotionPromotedIsFalse :
      ratioPromotionPromoted ≡ false

    noPromotionWithoutAuthority :
      MatterRepresentationPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open YukawaSectorRatioFormPromotionReceipt public

canonicalYukawaSectorRatioFormPromotionReceipt :
  YukawaSectorRatioFormPromotionReceipt
canonicalYukawaSectorRatioFormPromotionReceipt =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; ratioPromotionTargets =
        canonicalYukawaRatioPromotionTargets
    ; ratioPromotionTargetsAreCanonical =
        refl
    ; georgiJarlskogRelations =
        canonicalGeorgiJarlskogRelationLabels
    ; georgiJarlskogRelationsAreCanonical =
        refl
    ; froggattNielsenChargeSlots =
        canonicalFroggattNielsenChargeSlots
    ; froggattNielsenChargeSlotsAreCanonical =
        refl
    ; ckmWolfensteinFNRelations =
        canonicalCKMWolfensteinFNRelationLabels
    ; ckmWolfensteinFNRelationsAreCanonical =
        refl
    ; frobeniusPhaseCPSources =
        canonicalFrobeniusPhaseCPSourceLabels
    ; frobeniusPhaseCPSourcesAreCanonical =
        refl
    ; pmnsMajoranaP7SU2RTargets =
        canonicalPMNSMajoranaP7SU2RTargets
    ; pmnsMajoranaP7SU2RTargetsAreCanonical =
        refl
    ; seesawScaleReceipts =
        canonicalSeesawScaleReceiptLabels
    ; seesawScaleReceiptsAreCanonical =
        refl
    ; p7SeesawLane =
        Moonshine.p7
    ; p7SeesawLaneIsCanonical =
        refl
    ; p7HighEnergyAssignment =
        FractranLane.assignedSU2RBrokenAtSeesaw
    ; p7HighEnergyAssignmentIsSU2RBrokenAtSeesaw =
        refl
    ; ratioFormPromotionTargetRecorded =
        true
    ; ratioFormPromotionTargetRecordedIsTrue =
        refl
    ; georgiJarlskogSU5FortyFiveRecorded =
        true
    ; georgiJarlskogSU5FortyFiveRecordedIsTrue =
        refl
    ; froggattNielsenTextureRecorded =
        true
    ; froggattNielsenTextureRecordedIsTrue =
        refl
    ; ckmWolfensteinCabibboFromFNRecorded =
        true
    ; ckmWolfensteinCabibboFromFNRecordedIsTrue =
        refl
    ; frobeniusPhaseCPSourceRecorded =
        true
    ; frobeniusPhaseCPSourceRecordedIsTrue =
        refl
    ; pmnsDemocraticMajoranaP7SU2RRecorded =
        true
    ; pmnsDemocraticMajoranaP7SU2RRecordedIsTrue =
        refl
    ; seesawScaleReceiptRecorded =
        true
    ; seesawScaleReceiptRecordedIsTrue =
        refl
    ; exactMatrixNumericsPromoted =
        false
    ; exactMatrixNumericsPromotedIsFalse =
        refl
    ; absoluteHiggsVEVOrFermionScaleDerived =
        false
    ; absoluteHiggsVEVOrFermionScaleDerivedIsFalse =
        refl
    ; adapter4AbsoluteScaleBoundary =
        "absolute Higgs vev, running fermion masses, thresholds, and physical mass scale remain Adapter 4 authority inputs"
    ; ratioPromotionPromoted =
        false
    ; ratioPromotionPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "Yukawa sector is recorded as ratio-form promotion target data, not absolute mass numerics"
        ∷ "Georgi-Jarlskog relations are symbolic SU(5)+45-Higgs Clebsch relation labels"
        ∷ "Froggatt-Nielsen textures are symbolic charge-slot and lambda-power targets"
        ∷ "The FN sketch q_p = v_p(|M|)-2 leaves q_H as Adapter4 normalisation input and does not resolve top-Yukawa charge neutrality"
        ∷ "CKM Wolfenstein/Cabibbo hierarchy is recorded as arising from FN left-quark charge differences"
        ∷ "CP violation has a Frobenius-phase source socket without a promoted numeric phase"
        ∷ "PMNS target uses a democratic Majorana texture sourced by p7 SU2R broken at seesaw"
        ∷ "Seesaw scale is a receipt target; exact matrices and absolute Higgs vev/fermion scales remain Adapter 4"
        ∷ []
    }

record MatterPrimeLaneReceiptTargetSurface : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    matterPrimeLaneTargets :
      List MatterPrimeLaneTarget

    matterPrimeLaneTargetsAreCanonical :
      matterPrimeLaneTargets
      ≡
      canonicalMatterPrimeLaneTargets

    trackedPrimeLane :
      List Moonshine.MonsterPrimeLane

    trackedPrimeLaneAreCanonical :
      trackedPrimeLane
      ≡
      Moonshine.canonicalMonsterPrimeLane

    dhrGaugeReceiptSurface :
      DHR.DHRGaugeReceiptSurface

    dhrEndomorphismTarget :
      Moonshine.MonsterPrimeLane →
      DHR.LocalisedEndomorphism →
      Set

    dhrTransportTarget :
      (p : Moonshine.MonsterPrimeLane) →
      (ρ : DHR.LocalisedEndomorphism) →
      DHR.Transportable ρ →
      Set

    matterSectorTarget :
      Moonshine.MonsterPrimeLane →
      StandardModelMatterSectorTarget →
      MatterRepresentation →
      Set

    conjecturalLaneDimension :
      Moonshine.MonsterPrimeLane →
      Nat

    laneDimension2Is1 :
      conjecturalLaneDimension Moonshine.p2 ≡ 1

    laneDimension3Is2 :
      conjecturalLaneDimension Moonshine.p3 ≡ 2

    laneDimension5Is3 :
      conjecturalLaneDimension Moonshine.p5 ≡ 3

    laneDimensionAtLeast11Is0 :
      (p : Moonshine.MonsterPrimeLane) →
      Moonshine.MonsterPrimeLaneAtLeast11 p →
      conjecturalLaneDimension p ≡ 0

    highEnergyPatiSalamAssignmentBridge :
      Moonshine.MonsterPrimeLane →
      FractranLane.HighEnergyPatiSalamLaneAssignment

    highEnergyPatiSalamAssignmentBridgeIsCanonical :
      highEnergyPatiSalamAssignmentBridge
      ≡
      FractranLane.patiSalamHighEnergyAssignment

    highEnergyPatiSalamP2IsU1 :
      highEnergyPatiSalamAssignmentBridge Moonshine.p2
      ≡
      FractranLane.assignedU1

    highEnergyPatiSalamP3IsSU2L :
      highEnergyPatiSalamAssignmentBridge Moonshine.p3
      ≡
      FractranLane.assignedSU2L

    highEnergyPatiSalamP5IsSU3c :
      highEnergyPatiSalamAssignmentBridge Moonshine.p5
      ≡
      FractranLane.assignedSU3c

    highEnergyPatiSalamP7IsSU2RBrokenAtSeesaw :
      highEnergyPatiSalamAssignmentBridge Moonshine.p7
      ≡
      FractranLane.assignedSU2RBrokenAtSeesaw

    highEnergyPatiSalamAtLeast11InactiveOrMatter :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      highEnergyPatiSalamAssignmentBridge p
      ≡
      FractranLane.inactiveOrMatterLane

    laneDimensionTableInternallyPromoted :
      Bool

    laneDimensionTableInternallyPromotedIsTrue :
      laneDimensionTableInternallyPromoted ≡ true

    matterPrimeLaneDerived :
      Bool

    matterPrimeLaneDerivedIsFalse :
      matterPrimeLaneDerived ≡ false

    highEnergyBridgeDerivesMatterRepresentations :
      Bool

    highEnergyBridgeDerivesMatterRepresentationsIsFalse :
      highEnergyBridgeDerivesMatterRepresentations ≡ false

    highEnergyBridgeIsDHRLaneDimension :
      Bool

    highEnergyBridgeIsDHRLaneDimensionIsFalse :
      highEnergyBridgeIsDHRLaneDimension ≡ false

    receiptBoundary :
      List String

open MatterPrimeLaneReceiptTargetSurface public

canonicalMatterPrimeLaneReceiptTargetSurface :
  MatterPrimeLaneReceiptTargetSurface
canonicalMatterPrimeLaneReceiptTargetSurface =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; matterPrimeLaneTargets =
        canonicalMatterPrimeLaneTargets
    ; matterPrimeLaneTargetsAreCanonical =
        refl
    ; trackedPrimeLane =
        Moonshine.canonicalMonsterPrimeLane
    ; trackedPrimeLaneAreCanonical =
        refl
    ; dhrGaugeReceiptSurface =
        DHR.canonicalDHRGaugeReceiptSurface
    ; dhrEndomorphismTarget =
        abstractMatterPrimeLaneDHREndoTarget
    ; dhrTransportTarget =
        abstractMatterPrimeLaneTransportTarget
    ; matterSectorTarget =
        abstractMatterPrimeLaneSectorTarget
    ; conjecturalLaneDimension =
        Moonshine.monsterPrimeLaneConjecturalDHRDimension
    ; laneDimension2Is1 =
        refl
    ; laneDimension3Is2 =
        refl
    ; laneDimension5Is3 =
        refl
    ; laneDimensionAtLeast11Is0 =
        Moonshine.monsterPrimeLaneDHRDimensionAtLeast11Is0
    ; highEnergyPatiSalamAssignmentBridge =
        FractranLane.patiSalamHighEnergyAssignment
    ; highEnergyPatiSalamAssignmentBridgeIsCanonical =
        refl
    ; highEnergyPatiSalamP2IsU1 =
        refl
    ; highEnergyPatiSalamP3IsSU2L =
        refl
    ; highEnergyPatiSalamP5IsSU3c =
        refl
    ; highEnergyPatiSalamP7IsSU2RBrokenAtSeesaw =
        refl
    ; highEnergyPatiSalamAtLeast11InactiveOrMatter =
        FractranLane.patiSalamAtLeast11IsInactiveOrMatter
    ; laneDimensionTableInternallyPromoted =
        true
    ; laneDimensionTableInternallyPromotedIsTrue =
        refl
    ; matterPrimeLaneDerived =
        false
    ; matterPrimeLaneDerivedIsFalse =
        refl
    ; highEnergyBridgeDerivesMatterRepresentations =
        false
    ; highEnergyBridgeDerivesMatterRepresentationsIsFalse =
        refl
    ; highEnergyBridgeIsDHRLaneDimension =
        false
    ; highEnergyBridgeIsDHRLaneDimensionIsFalse =
        refl
    ; receiptBoundary =
        "Matter prime-lane receipt target binds DHR localized endomorphism targets to SM matter-sector representation targets"
        ∷ "The DHR lane dimension assignment now records the DLM-compatible table: 2->1, 3->2, 5->3, 7->2, primes >=11 -> 0"
        ∷ "A separate conjectural high-energy Pati-Salam bridge records p2->U1, p3->SU2L, p5->SU3c, p7->SU2R-broken-at-seesaw, and p>=11 inactive/matter"
        ∷ "The supersingular-prime-to-gauge-factor assignment is a DASHI-specific bridge, not a first-principles theorem"
        ∷ "The high-energy bridge does not compute DHR laneDimension and does not derive matter representations"
        ∷ "No matter representation, hypercharge assignment, anomaly proof, or gauge-group equality is derived here"
        ∷ []
    }

record MatterPrimeLaneReceipt : Setω where
  field
    targetSurface :
      MatterPrimeLaneReceiptTargetSurface

    targetSurfaceIsCanonical :
      Bool

    targetSurfaceIsCanonicalIsTrue :
      targetSurfaceIsCanonical ≡ true

open MatterPrimeLaneReceipt public

canonicalMatterPrimeLaneReceipt :
  MatterPrimeLaneReceipt
canonicalMatterPrimeLaneReceipt =
  record
    { targetSurface =
        canonicalMatterPrimeLaneReceiptTargetSurface
    ; targetSurfaceIsCanonical =
        true
    ; targetSurfaceIsCanonicalIsTrue =
        refl
    }

record MatterRepresentationBoundaryReceipt : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    matterSectorTargets :
      List StandardModelMatterSectorTarget

    matterSectorTargetsAreCanonical :
      matterSectorTargets
      ≡
      canonicalStandardModelMatterSectorTargets

    adapterBoundaries :
      List MatterAdapterBoundary

    adapterBoundariesAreCanonical :
      adapterBoundaries
      ≡
      canonicalMatterAdapterBoundaries

    compactGroupBoundary :
      String

    representationCategoryBoundary :
      String

    hyperchargeAnomalyBoundary :
      String

    generationYukawaMixingBoundary :
      String

    yukawaRatioFormPromotionReceipt :
      YukawaSectorRatioFormPromotionReceipt

    standardModelDerived :
      Bool

    standardModelDerivedIsFalse :
      standardModelDerived ≡ false

    yukawaSectorDerived :
      Bool

    yukawaSectorDerivedIsFalse :
      yukawaSectorDerived ≡ false

    boundaryPromoted :
      Bool

    boundaryPromotedIsFalse :
      boundaryPromoted ≡ false

    noPromotionWithoutAuthority :
      MatterRepresentationPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open MatterRepresentationBoundaryReceipt public

canonicalMatterRepresentationBoundaryReceipt :
  MatterRepresentationBoundaryReceipt
canonicalMatterRepresentationBoundaryReceipt =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; matterSectorTargets =
        canonicalStandardModelMatterSectorTargets
    ; matterSectorTargetsAreCanonical =
        refl
    ; adapterBoundaries =
        canonicalMatterAdapterBoundaries
    ; adapterBoundariesAreCanonical =
        refl
    ; compactGroupBoundary =
        "compact gauge group and global form must be supplied before matter representations are promoted"
    ; representationCategoryBoundary =
        "representation category and chirality/conjugation conventions are target data, not derived here"
    ; hyperchargeAnomalyBoundary =
        "hypercharge normalization and anomaly-cancellation equations are named obligations, not solved equations here"
    ; generationYukawaMixingBoundary =
        "three generations, Yukawa matrices, CKM, PMNS, and neutrino masses remain adapter boundaries"
    ; yukawaRatioFormPromotionReceipt =
        canonicalYukawaSectorRatioFormPromotionReceipt
    ; standardModelDerived =
        false
    ; standardModelDerivedIsFalse =
        refl
    ; yukawaSectorDerived =
        false
    ; yukawaSectorDerivedIsFalse =
        refl
    ; boundaryPromoted =
        false
    ; boundaryPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "MatterRepresentationBoundaryReceipt is a non-promoting receipt for SM matter-representation sockets"
        ∷ "it does not derive the Standard Model group, hypercharges, generations, Yukawa sector, CKM, PMNS, or neutrino sector"
        ∷ "Yukawa ratio-form target data may be recorded symbolically, but absolute Higgs vev and fermion scales remain Adapter 4"
        ∷ "it may be cited only as an explicit adapter-boundary receipt"
        ∷ []
    }

record MatterRepresentationReceiptSurface : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    matterBoundaryReceipt :
      MatterRepresentationBoundaryReceipt

    matterPrimeLaneReceiptTarget :
      MatterPrimeLaneReceiptTargetSurface

    matterPrimeLaneYukawaFNReceipt :
      MatterPrimeLaneYukawaFNReceipt

    matterSectorTargets :
      List StandardModelMatterSectorTarget

    matterSectorTargetsAreCanonical :
      matterSectorTargets
      ≡
      canonicalStandardModelMatterSectorTargets

    hyperchargeAnomalyConditions :
      List HyperchargeAnomalyConditionLabel

    hyperchargeAnomalyConditionsAreCanonical :
      hyperchargeAnomalyConditions
      ≡
      canonicalHyperchargeAnomalyConditionLabels

    adapterBoundaries :
      List MatterAdapterBoundary

    adapterBoundariesAreCanonical :
      adapterBoundaries
      ≡
      canonicalMatterAdapterBoundaries

    compactGaugeGroupTarget :
      Set

    matterRepresentationTarget :
      Set

    hyperchargeAssignmentTargetCarrier :
      Set

    anomalyClassTargetCarrier :
      Set

    generationStructureTarget :
      Set

    yukawaSectorTarget :
      Set

    ckmMatrixTarget :
      Set

    pmnsMatrixTarget :
      Set

    neutrinoSectorTarget :
      Set

    yukawaRatioFormPromotionReceipt :
      YukawaSectorRatioFormPromotionReceipt

    l3SMRepresentationTableReceipt :
      L3SMRepresentationTableReceipt

    representationAdapter :
      compactGaugeGroupTarget →
      StandardModelMatterSectorTarget →
      matterRepresentationTarget

    hyperchargeAdapter :
      StandardModelMatterSectorTarget →
      hyperchargeAssignmentTargetCarrier

    anomalyClassAdapter :
      hyperchargeAssignmentTargetCarrier →
      anomalyClassTargetCarrier

    anomalyEquationLabels :
      List String

    threeGenerationBoundary :
      String

    yukawaCKMPMNSNeutrinoBoundary :
      String

    adapter4AbsoluteHiggsVEVFermionScaleBoundary :
      String

    matterSurfaceHiggsDoubletPrimitive :
      HiggsDoubletPrimitive

    matterSurfaceHiggsDoubletPrimitiveIsCanonical :
      matterSurfaceHiggsDoubletPrimitive
      ≡
      canonicalHiggsDoubletPrimitive

    matterSurfaceLeftQuarkDoubletFamilyPrimitive :
      LeftQuarkDoubletFamilyPrimitive

    matterSurfaceLeftQuarkDoubletFamilyPrimitiveIsCanonical :
      matterSurfaceLeftQuarkDoubletFamilyPrimitive
      ≡
      canonicalLeftQuarkDoubletFamilyPrimitive

    matterSurfaceRightUpQuarkFamilyPrimitive :
      RightUpQuarkFamilyPrimitive

    matterSurfaceRightUpQuarkFamilyPrimitiveIsCanonical :
      matterSurfaceRightUpQuarkFamilyPrimitive
      ≡
      canonicalRightUpQuarkFamilyPrimitive

    matterSurfaceRightDownQuarkFamilyPrimitive :
      RightDownQuarkFamilyPrimitive

    matterSurfaceRightDownQuarkFamilyPrimitiveIsCanonical :
      matterSurfaceRightDownQuarkFamilyPrimitive
      ≡
      canonicalRightDownQuarkFamilyPrimitive

    matterSurfaceLeftLeptonDoubletFamilyPrimitive :
      LeftLeptonDoubletFamilyPrimitive

    matterSurfaceLeftLeptonDoubletFamilyPrimitiveIsCanonical :
      matterSurfaceLeftLeptonDoubletFamilyPrimitive
      ≡
      canonicalLeftLeptonDoubletFamilyPrimitive

    matterSurfaceRightChargedLeptonFamilyPrimitive :
      RightChargedLeptonFamilyPrimitive

    matterSurfaceRightChargedLeptonFamilyPrimitiveIsCanonical :
      matterSurfaceRightChargedLeptonFamilyPrimitive
      ≡
      canonicalRightChargedLeptonFamilyPrimitive

    matterSurfaceThreeGenerationStructure :
      GenerationStructure

    matterSurfaceThreeGenerationStructureIsCanonical :
      matterSurfaceThreeGenerationStructure
      ≡
      canonicalThreeGenerationStructure

    matterSurfaceHiggsDoubletMatterRepresentation :
      MatterRepresentation

    matterSurfaceHiggsDoubletMatterRepresentationIsCanonical :
      matterSurfaceHiggsDoubletMatterRepresentation
      ≡
      canonicalHiggsDoubletMatterRepresentation

    matterSurfaceLeftQuarkDoubletFamilyMatterRepresentation :
      MatterRepresentation

    matterSurfaceLeftQuarkDoubletFamilyMatterRepresentationIsCanonical :
      matterSurfaceLeftQuarkDoubletFamilyMatterRepresentation
      ≡
      canonicalLeftQuarkDoubletFamilyMatterRepresentation

    matterSurfaceRightUpQuarkFamilyMatterRepresentation :
      MatterRepresentation

    matterSurfaceRightUpQuarkFamilyMatterRepresentationIsCanonical :
      matterSurfaceRightUpQuarkFamilyMatterRepresentation
      ≡
      canonicalRightUpQuarkFamilyMatterRepresentation

    matterSurfaceRightDownQuarkFamilyMatterRepresentation :
      MatterRepresentation

    matterSurfaceRightDownQuarkFamilyMatterRepresentationIsCanonical :
      matterSurfaceRightDownQuarkFamilyMatterRepresentation
      ≡
      canonicalRightDownQuarkFamilyMatterRepresentation

    matterSurfaceLeftLeptonDoubletFamilyMatterRepresentation :
      MatterRepresentation

    matterSurfaceLeftLeptonDoubletFamilyMatterRepresentationIsCanonical :
      matterSurfaceLeftLeptonDoubletFamilyMatterRepresentation
      ≡
      canonicalLeftLeptonDoubletFamilyMatterRepresentation

    matterSurfaceRightChargedLeptonFamilyMatterRepresentation :
      MatterRepresentation

    matterSurfaceRightChargedLeptonFamilyMatterRepresentationIsCanonical :
      matterSurfaceRightChargedLeptonFamilyMatterRepresentation
      ≡
      canonicalRightChargedLeptonFamilyMatterRepresentation

    matterRepresentationConstructorsSuppliedBelowW4 :
      Bool

    matterRepresentationConstructorsSuppliedBelowW4IsTrue :
      matterRepresentationConstructorsSuppliedBelowW4 ≡ true

    generationStructureConstructorSuppliedBelowW4 :
      Bool

    generationStructureConstructorSuppliedBelowW4IsTrue :
      generationStructureConstructorSuppliedBelowW4 ≡ true

    matterRepresentationPrimitivesConstructedBelowW4 :
      Bool

    matterRepresentationPrimitivesConstructedBelowW4IsTrue :
      matterRepresentationPrimitivesConstructedBelowW4 ≡ true

    matterRepresentationsDerived :
      Bool

    matterRepresentationsDerivedIsFalse :
      matterRepresentationsDerived ≡ false

    noPromotionWithoutAuthority :
      MatterRepresentationPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open MatterRepresentationReceiptSurface public

canonicalMatterRepresentationReceiptSurface :
  MatterRepresentationReceiptSurface
canonicalMatterRepresentationReceiptSurface =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; matterBoundaryReceipt =
        canonicalMatterRepresentationBoundaryReceipt
    ; matterPrimeLaneReceiptTarget =
        canonicalMatterPrimeLaneReceiptTargetSurface
    ; matterPrimeLaneYukawaFNReceipt =
        canonicalMatterPrimeLaneYukawaFNReceipt
    ; matterSectorTargets =
        canonicalStandardModelMatterSectorTargets
    ; matterSectorTargetsAreCanonical =
        refl
    ; hyperchargeAnomalyConditions =
        canonicalHyperchargeAnomalyConditionLabels
    ; hyperchargeAnomalyConditionsAreCanonical =
        refl
    ; adapterBoundaries =
        canonicalMatterAdapterBoundaries
    ; adapterBoundariesAreCanonical =
        refl
    ; compactGaugeGroupTarget =
        CompactGaugeGroup
    ; matterRepresentationTarget =
        MatterRepresentation
    ; hyperchargeAssignmentTargetCarrier =
        HyperchargeAssignment
    ; anomalyClassTargetCarrier =
        AnomalyClass
    ; generationStructureTarget =
        GenerationStructure
    ; yukawaSectorTarget =
        YukawaSector
    ; ckmMatrixTarget =
        MixingMatrix
    ; pmnsMatrixTarget =
        MixingMatrix
    ; neutrinoSectorTarget =
        NeutrinoSector
    ; yukawaRatioFormPromotionReceipt =
        canonicalYukawaSectorRatioFormPromotionReceipt
    ; l3SMRepresentationTableReceipt =
        canonicalL3SMRepresentationTableReceipt
    ; representationAdapter =
        matterRepresentationAdapterTarget
    ; hyperchargeAdapter =
        hyperchargeAssignmentTarget
    ; anomalyClassAdapter =
        anomalyClassTarget
    ; anomalyEquationLabels =
        "SU(3)^2-U(1)_Y anomaly cancellation"
        ∷ "SU(2)^2-U(1)_Y anomaly cancellation"
        ∷ "U(1)_Y^3 anomaly cancellation"
        ∷ "gravity^2-U(1)_Y anomaly cancellation"
        ∷ "global SU(2) Witten anomaly even-doublet condition"
        ∷ []
    ; threeGenerationBoundary =
        "proposed three-generation grouping remains incomplete/open because generation 3 has only {47,59,71} plus a missing/right-neutrino ambiguity"
    ; yukawaCKMPMNSNeutrinoBoundary =
        "Yukawa ratio textures, CKM, PMNS, and neutrino masses/mixings are symbolic receipt targets, not promoted matrix numerics"
    ; adapter4AbsoluteHiggsVEVFermionScaleBoundary =
        "absolute Higgs vev, q_H Higgs FN charge normalisation, and fermion mass scale remain Adapter 4 authority inputs"
    ; matterSurfaceHiggsDoubletPrimitive =
        canonicalHiggsDoubletPrimitive
    ; matterSurfaceHiggsDoubletPrimitiveIsCanonical =
        refl
    ; matterSurfaceLeftQuarkDoubletFamilyPrimitive =
        canonicalLeftQuarkDoubletFamilyPrimitive
    ; matterSurfaceLeftQuarkDoubletFamilyPrimitiveIsCanonical =
        refl
    ; matterSurfaceRightUpQuarkFamilyPrimitive =
        canonicalRightUpQuarkFamilyPrimitive
    ; matterSurfaceRightUpQuarkFamilyPrimitiveIsCanonical =
        refl
    ; matterSurfaceRightDownQuarkFamilyPrimitive =
        canonicalRightDownQuarkFamilyPrimitive
    ; matterSurfaceRightDownQuarkFamilyPrimitiveIsCanonical =
        refl
    ; matterSurfaceLeftLeptonDoubletFamilyPrimitive =
        canonicalLeftLeptonDoubletFamilyPrimitive
    ; matterSurfaceLeftLeptonDoubletFamilyPrimitiveIsCanonical =
        refl
    ; matterSurfaceRightChargedLeptonFamilyPrimitive =
        canonicalRightChargedLeptonFamilyPrimitive
    ; matterSurfaceRightChargedLeptonFamilyPrimitiveIsCanonical =
        refl
    ; matterSurfaceThreeGenerationStructure =
        canonicalThreeGenerationStructure
    ; matterSurfaceThreeGenerationStructureIsCanonical =
        refl
    ; matterSurfaceHiggsDoubletMatterRepresentation =
        canonicalHiggsDoubletMatterRepresentation
    ; matterSurfaceHiggsDoubletMatterRepresentationIsCanonical =
        refl
    ; matterSurfaceLeftQuarkDoubletFamilyMatterRepresentation =
        canonicalLeftQuarkDoubletFamilyMatterRepresentation
    ; matterSurfaceLeftQuarkDoubletFamilyMatterRepresentationIsCanonical =
        refl
    ; matterSurfaceRightUpQuarkFamilyMatterRepresentation =
        canonicalRightUpQuarkFamilyMatterRepresentation
    ; matterSurfaceRightUpQuarkFamilyMatterRepresentationIsCanonical =
        refl
    ; matterSurfaceRightDownQuarkFamilyMatterRepresentation =
        canonicalRightDownQuarkFamilyMatterRepresentation
    ; matterSurfaceRightDownQuarkFamilyMatterRepresentationIsCanonical =
        refl
    ; matterSurfaceLeftLeptonDoubletFamilyMatterRepresentation =
        canonicalLeftLeptonDoubletFamilyMatterRepresentation
    ; matterSurfaceLeftLeptonDoubletFamilyMatterRepresentationIsCanonical =
        refl
    ; matterSurfaceRightChargedLeptonFamilyMatterRepresentation =
        canonicalRightChargedLeptonFamilyMatterRepresentation
    ; matterSurfaceRightChargedLeptonFamilyMatterRepresentationIsCanonical =
        refl
    ; matterRepresentationConstructorsSuppliedBelowW4 =
        true
    ; matterRepresentationConstructorsSuppliedBelowW4IsTrue =
        refl
    ; generationStructureConstructorSuppliedBelowW4 =
        true
    ; generationStructureConstructorSuppliedBelowW4IsTrue =
        refl
    ; matterRepresentationPrimitivesConstructedBelowW4 =
        true
    ; matterRepresentationPrimitivesConstructedBelowW4IsTrue =
        refl
    ; matterRepresentationsDerived =
        false
    ; matterRepresentationsDerivedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "SM matter representations are target/adaptation sockets only"
        ∷ "matter prime-lane DHR receipt target is present but conjectural/open and non-promoting"
        ∷ "Tranche 2 matter-lane/Yukawa FN receipt records gauge lanes {2,3,5,7} and the eleven listed p>=11 matter lanes {11,13,17,19,23,29,31,41,47,59,71}; it does not promote a twelfth lane"
        ∷ "Pati-Salam matter target context is (4,2,1) plus (bar4,1,2), with 4 -> 3_{1/3} + 1_{-1}"
        ∷ "Proposed grouping is {11,13,17,19}, {23,29,31,41}, {47,59,71}; generation 3 remains incomplete/open due to the missing/right-neutrino ambiguity"
        ∷ "hypercharge and anomaly equations are labels for future proofs, not solved equations here"
        ∷ "Yukawa ratio-form target records SU(5)+45 Georgi-Jarlskog, FN texture, CKM Wolfenstein/Cabibbo, Frobenius CP, p7 SU2R PMNS, and seesaw-scale sockets"
        ∷ "L3 representation-table receipt records seven SMParticle rows; the right-neutrino row is staged and blocked on missing canonical sector/lane authority"
        ∷ "FN accounting records q_p = v_p(|M|)-2 and leaves the top-Yukawa/Higgs-charge inconsistency to q_H Adapter4 normalisation"
        ∷ "Matter-surface constructors build canonical Higgs, left/right quark, and left/right charged-lepton MatterRepresentation witnesses from local gauge/hypercharge/chirality primitives, plus a canonical three-generation GenerationStructure witness"
        ∷ "The generic representation adapter remains an adapter constructor over a supplied compact group and sector; it is not an external calibration or derivation"
        ∷ "three generations, exact Yukawa matrices, CKM/PMNS numerics, neutrino masses, Higgs vev, and fermion scale remain irreducible adapter boundaries"
        ∷ "no Standard Model, GRQFT, or TOE claim is promoted"
        ∷ []
    }

------------------------------------------------------------------------
-- lower6 l3: explicit Standard Model table surface.
--
-- This is a concrete table over the repository's existing representation and
-- hypercharge primitives.  It records the finite multiplet assignment data but
-- does not prove the prime-lane carrier functor or Standard Model group match.

data SMTableSpinStatistics : Set where
  smFermion :
    SMTableSpinStatistics

  smBoson :
    SMTableSpinStatistics

data SMTableSectorKind : Set where
  smMatterSector :
    StandardModelMatterSectorTarget →
    SMTableSectorKind

  smGaugeBosonSector :
    String →
    SMTableSectorKind

record SMParticleTableRow : Set where
  constructor smParticleTableRow
  field
    primeLane :
      Nat

    sectorKind :
      SMTableSectorKind

    su3Representation :
      GaugeRepresentationPrimitive

    su2Representation :
      GaugeRepresentationPrimitive

    hypercharge :
      HyperchargePrimitive

    spinStatistics :
      SMTableSpinStatistics

open SMParticleTableRow public

smLeftQuarkDoubletRow : SMParticleTableRow
smLeftQuarkDoubletRow =
  smParticleTableRow
    2
    (smMatterSector leftQuarkDoubletTarget)
    canonicalSU3ColourTripletPrimitive
    canonicalSU2LWeakDoubletPrimitive
    canonicalHyperchargeOneSixthPrimitive
    smFermion

smRightUpQuarkRow : SMParticleTableRow
smRightUpQuarkRow =
  smParticleTableRow
    3
    (smMatterSector rightUpQuarkTarget)
    canonicalSU3ColourTripletPrimitive
    canonicalSU2LWeakSingletPrimitive
    canonicalHyperchargeTwoThirdsPrimitive
    smFermion

smLeftLeptonDoubletRow : SMParticleTableRow
smLeftLeptonDoubletRow =
  smParticleTableRow
    5
    (smMatterSector leftLeptonDoubletTarget)
    canonicalSU3ColourSingletPrimitive
    canonicalSU2LWeakDoubletPrimitive
    canonicalHyperchargeMinusOneHalfPrimitive
    smFermion

smRightChargedLeptonRow : SMParticleTableRow
smRightChargedLeptonRow =
  smParticleTableRow
    7
    (smMatterSector rightChargedLeptonTarget)
    canonicalSU3ColourSingletPrimitive
    canonicalSU2LWeakSingletPrimitive
    canonicalHyperchargeMinusOnePrimitive
    smFermion

smPhotonRow : SMParticleTableRow
smPhotonRow =
  smParticleTableRow
    11
    (smGaugeBosonSector "photon")
    canonicalSU3ColourSingletPrimitive
    canonicalSU2LWeakSingletPrimitive
    canonicalHyperchargeZeroPrimitive
    smBoson

smWeakBosonRow : SMParticleTableRow
smWeakBosonRow =
  smParticleTableRow
    13
    (smGaugeBosonSector "weak-boson-adjoint")
    canonicalSU3ColourSingletPrimitive
    canonicalSU2LWeakDoubletPrimitive
    canonicalHyperchargeZeroPrimitive
    smBoson

smGluonRow : SMParticleTableRow
smGluonRow =
  smParticleTableRow
    17
    (smGaugeBosonSector "gluon-adjoint")
    canonicalSU3ColourTripletPrimitive
    canonicalSU2LWeakSingletPrimitive
    canonicalHyperchargeZeroPrimitive
    smBoson

smParticleTable : List SMParticleTableRow
smParticleTable =
  smLeftQuarkDoubletRow
  ∷ smRightUpQuarkRow
  ∷ smLeftLeptonDoubletRow
  ∷ smRightChargedLeptonRow
  ∷ smPhotonRow
  ∷ smWeakBosonRow
  ∷ smGluonRow
  ∷ []

data SMParticleTableMatchBlocker : Set where
  missingPrimeLaneSMQuantumNumberAgreement :
    SMParticleTableMatchBlocker

record SMParticleTableCurrentWaveReceipt : Setω where
  field
    table :
      List SMParticleTableRow

    tableIsCanonical :
      table ≡ smParticleTable

    matterRowsUseExistingMatterTargets :
      Bool

    matterRowsUseExistingMatterTargetsIsTrue :
      matterRowsUseExistingMatterTargets ≡ true

    gaugeRowsRecordedAsTableRows :
      Bool

    gaugeRowsRecordedAsTableRowsIsTrue :
      gaugeRowsRecordedAsTableRows ≡ true

    primeLaneQuantumNumberAgreementProved :
      Bool

    primeLaneQuantumNumberAgreementProvedIsFalse :
      primeLaneQuantumNumberAgreementProved ≡ false

    firstMatchBlocker :
      SMParticleTableMatchBlocker

    firstMatchBlockerIsPrimeLaneAgreement :
      firstMatchBlocker
      ≡
      missingPrimeLaneSMQuantumNumberAgreement

    exactStandardModelFunctorMatchPromoted :
      Bool

    exactStandardModelFunctorMatchPromotedIsFalse :
      exactStandardModelFunctorMatchPromoted ≡ false

    receiptBoundary :
      List String

open SMParticleTableCurrentWaveReceipt public

canonicalSMParticleTableCurrentWaveReceipt :
  SMParticleTableCurrentWaveReceipt
canonicalSMParticleTableCurrentWaveReceipt =
  record
    { table =
        smParticleTable
    ; tableIsCanonical =
        refl
    ; matterRowsUseExistingMatterTargets =
        true
    ; matterRowsUseExistingMatterTargetsIsTrue =
        refl
    ; gaugeRowsRecordedAsTableRows =
        true
    ; gaugeRowsRecordedAsTableRowsIsTrue =
        refl
    ; primeLaneQuantumNumberAgreementProved =
        false
    ; primeLaneQuantumNumberAgreementProvedIsFalse =
        refl
    ; firstMatchBlocker =
        missingPrimeLaneSMQuantumNumberAgreement
    ; firstMatchBlockerIsPrimeLaneAgreement =
        refl
    ; exactStandardModelFunctorMatchPromoted =
        false
    ; exactStandardModelFunctorMatchPromotedIsFalse =
        refl
    ; receiptBoundary =
        "l3 current wave records a seven-row SM particle/gauge table over the local primitive representation records"
        ∷ "The matter rows consume existing StandardModelMatterSectorTarget constructors and hypercharge primitives"
        ∷ "The gauge rows are explicit table rows only; the local representation surface has no adjoint gauge-boson representation constructor"
        ∷ "primeLaneSMQuantumNumberAgreement is still the first exact proof blocker"
        ∷ "No exact Standard Model carrier functor match is promoted"
        ∷ []
    }

------------------------------------------------------------------------
-- lower6/l3 Standard Model representation table surface.
--
-- The repository already has local primitive constructors for the usual SM
-- matter sockets.  This table packages them as receipt data only; it is not a
-- derivation of the SM gauge group, anomaly cancellation, CKM, or Yukawa
-- numerics.

data Lower6SMRepresentationTableRow : Set where
  lower6SMRowLeftQuarkDoublet :
    Lower6SMRepresentationTableRow

  lower6SMRowRightUpQuark :
    Lower6SMRepresentationTableRow

  lower6SMRowRightDownQuark :
    Lower6SMRepresentationTableRow

  lower6SMRowLeftLeptonDoublet :
    Lower6SMRepresentationTableRow

  lower6SMRowRightChargedLepton :
    Lower6SMRepresentationTableRow

  lower6SMRowHiggsDoublet :
    Lower6SMRepresentationTableRow

canonicalLower6SMRepresentationTableRows :
  List Lower6SMRepresentationTableRow
canonicalLower6SMRepresentationTableRows =
  lower6SMRowLeftQuarkDoublet
  ∷ lower6SMRowRightUpQuark
  ∷ lower6SMRowRightDownQuark
  ∷ lower6SMRowLeftLeptonDoublet
  ∷ lower6SMRowRightChargedLepton
  ∷ lower6SMRowHiggsDoublet
  ∷ []

record Lower6SMRepresentationTableReceipt : Setω where
  field
    lower6SMTableRows :
      List Lower6SMRepresentationTableRow

    lower6SMTableRowsAreCanonical :
      lower6SMTableRows ≡ canonicalLower6SMRepresentationTableRows

    lower6SMTableMatterTargets :
      List StandardModelMatterSectorTarget

    lower6SMTableMatterTargetsAreCanonical :
      lower6SMTableMatterTargets ≡ canonicalStandardModelMatterSectorTargets

    lower6SMTableThreeGenerationStructure :
      GenerationStructure

    lower6SMTableThreeGenerationStructureIsCanonical :
      lower6SMTableThreeGenerationStructure
      ≡
      canonicalThreeGenerationStructure

    lower6SMTableLeftQuarkRepresentation :
      MatterRepresentation

    lower6SMTableLeftQuarkRepresentationIsCanonical :
      lower6SMTableLeftQuarkRepresentation
      ≡
      canonicalLeftQuarkDoubletFamilyMatterRepresentation

    lower6SMTableRightUpRepresentation :
      MatterRepresentation

    lower6SMTableRightUpRepresentationIsCanonical :
      lower6SMTableRightUpRepresentation
      ≡
      canonicalRightUpQuarkFamilyMatterRepresentation

    lower6SMTableRightDownRepresentation :
      MatterRepresentation

    lower6SMTableRightDownRepresentationIsCanonical :
      lower6SMTableRightDownRepresentation
      ≡
      canonicalRightDownQuarkFamilyMatterRepresentation

    lower6SMTableLeftLeptonRepresentation :
      MatterRepresentation

    lower6SMTableLeftLeptonRepresentationIsCanonical :
      lower6SMTableLeftLeptonRepresentation
      ≡
      canonicalLeftLeptonDoubletFamilyMatterRepresentation

    lower6SMTableRightChargedLeptonRepresentation :
      MatterRepresentation

    lower6SMTableRightChargedLeptonRepresentationIsCanonical :
      lower6SMTableRightChargedLeptonRepresentation
      ≡
      canonicalRightChargedLeptonFamilyMatterRepresentation

    lower6SMTableHiggsRepresentation :
      MatterRepresentation

    lower6SMTableHiggsRepresentationIsCanonical :
      lower6SMTableHiggsRepresentation
      ≡
      canonicalHiggsDoubletMatterRepresentation

    lower6SMRepresentationTableRecorded :
      Bool

    lower6SMRepresentationTableRecordedIsTrue :
      lower6SMRepresentationTableRecorded ≡ true

    lower6SMRepresentationTablePromoted :
      Bool

    lower6SMRepresentationTablePromotedIsFalse :
      lower6SMRepresentationTablePromoted ≡ false

    lower6SMRepresentationTableBoundary :
      List String

open Lower6SMRepresentationTableReceipt public

canonicalLower6SMRepresentationTableReceipt :
  Lower6SMRepresentationTableReceipt
canonicalLower6SMRepresentationTableReceipt =
  record
    { lower6SMTableRows =
        canonicalLower6SMRepresentationTableRows
    ; lower6SMTableRowsAreCanonical =
        refl
    ; lower6SMTableMatterTargets =
        canonicalStandardModelMatterSectorTargets
    ; lower6SMTableMatterTargetsAreCanonical =
        refl
    ; lower6SMTableThreeGenerationStructure =
        canonicalThreeGenerationStructure
    ; lower6SMTableThreeGenerationStructureIsCanonical =
        refl
    ; lower6SMTableLeftQuarkRepresentation =
        canonicalLeftQuarkDoubletFamilyMatterRepresentation
    ; lower6SMTableLeftQuarkRepresentationIsCanonical =
        refl
    ; lower6SMTableRightUpRepresentation =
        canonicalRightUpQuarkFamilyMatterRepresentation
    ; lower6SMTableRightUpRepresentationIsCanonical =
        refl
    ; lower6SMTableRightDownRepresentation =
        canonicalRightDownQuarkFamilyMatterRepresentation
    ; lower6SMTableRightDownRepresentationIsCanonical =
        refl
    ; lower6SMTableLeftLeptonRepresentation =
        canonicalLeftLeptonDoubletFamilyMatterRepresentation
    ; lower6SMTableLeftLeptonRepresentationIsCanonical =
        refl
    ; lower6SMTableRightChargedLeptonRepresentation =
        canonicalRightChargedLeptonFamilyMatterRepresentation
    ; lower6SMTableRightChargedLeptonRepresentationIsCanonical =
        refl
    ; lower6SMTableHiggsRepresentation =
        canonicalHiggsDoubletMatterRepresentation
    ; lower6SMTableHiggsRepresentationIsCanonical =
        refl
    ; lower6SMRepresentationTableRecorded =
        true
    ; lower6SMRepresentationTableRecordedIsTrue =
        refl
    ; lower6SMRepresentationTablePromoted =
        false
    ; lower6SMRepresentationTablePromotedIsFalse =
        refl
    ; lower6SMRepresentationTableBoundary =
        "lower6/l3 records the available local SM representation rows as a table receipt"
        ∷ "rows cover Q_L, u_R, d_R, L_L, e_R, and H using existing MatterRepresentation constructors"
        ∷ "three-generation structure is canonical where applicable"
        ∷ "the table is not an SM gauge-group derivation, anomaly proof, Yukawa matrix, or CKM theorem"
        ∷ []
    }

lower6SMRepresentationTableDoesNotPromote :
  lower6SMRepresentationTablePromoted
    canonicalLower6SMRepresentationTableReceipt
  ≡
  false
lower6SMRepresentationTableDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Matter-side socket for the concrete carrier CKM/Yukawa wiring.
--
-- This surface cannot import the downstream CKM modules without creating an
-- import cycle.  It therefore exposes the matter-side socket in local terms:
-- the same concrete `MixingMatrix` carrier, the supplied quark/Higgs
-- representation constructors, and fail-closed blockers for the physical
-- promotion gaps that remain outside this module.

data MatterYukawaCKMWiringBlocker : Set where
  missingAbsoluteHiggsVEVW4Calibration :
    MatterYukawaCKMWiringBlocker

  missingGenericYukawaSplittingField :
    MatterYukawaCKMWiringBlocker

  missingNonDiagonalYukawaEigenbasis :
    MatterYukawaCKMWiringBlocker

  missingPhysicalCKMBasisIdentification :
    MatterYukawaCKMWiringBlocker

canonicalMatterYukawaCKMWiringBlockers :
  List MatterYukawaCKMWiringBlocker
canonicalMatterYukawaCKMWiringBlockers =
  missingAbsoluteHiggsVEVW4Calibration
  ∷ missingGenericYukawaSplittingField
  ∷ missingNonDiagonalYukawaEigenbasis
  ∷ missingPhysicalCKMBasisIdentification
  ∷ []

record MatterCarrierYukawaCKMWiringReceipt : Setω where
  field
    matterReceipt :
      MatterRepresentationReceiptSurface

    leftQuarkMatterRepresentation :
      MatterRepresentation

    leftQuarkMatterRepresentationIsCanonical :
      leftQuarkMatterRepresentation
      ≡
      canonicalLeftQuarkDoubletFamilyMatterRepresentation

    rightUpMatterRepresentation :
      MatterRepresentation

    rightUpMatterRepresentationIsCanonical :
      rightUpMatterRepresentation
      ≡
      canonicalRightUpQuarkFamilyMatterRepresentation

    rightDownMatterRepresentation :
      MatterRepresentation

    rightDownMatterRepresentationIsCanonical :
      rightDownMatterRepresentation
      ≡
      canonicalRightDownQuarkFamilyMatterRepresentation

    higgsMatterRepresentation :
      MatterRepresentation

    higgsMatterRepresentationIsCanonical :
      higgsMatterRepresentation
      ≡
      canonicalHiggsDoubletMatterRepresentation

    threeGenerationStructure :
      GenerationStructure

    threeGenerationStructureIsCanonical :
      threeGenerationStructure
      ≡
      canonicalThreeGenerationStructure

    carrierCKMMatrix :
      MixingMatrix

    carrierCKMMatrixIsIdentity :
      carrierCKMMatrix ≡ identityMixingMatrix

    carrierYukawaMatrixTarget :
      Set

    carrierYukawaMatrixTargetIsMixingMatrix :
      carrierYukawaMatrixTarget ≡ MixingMatrix

    blockers :
      List MatterYukawaCKMWiringBlocker

    blockersAreCanonical :
      blockers ≡ canonicalMatterYukawaCKMWiringBlockers

    firstBlocker :
      MatterYukawaCKMWiringBlocker

    firstBlockerIsAbsoluteHiggsVEVW4 :
      firstBlocker ≡ missingAbsoluteHiggsVEVW4Calibration

    absoluteHiggsVEVW4Calibrated :
      Bool

    absoluteHiggsVEVW4CalibratedIsFalse :
      absoluteHiggsVEVW4Calibrated ≡ false

    splittingFieldEigenbasisConstructed :
      Bool

    splittingFieldEigenbasisConstructedIsFalse :
      splittingFieldEigenbasisConstructed ≡ false

    physicalCKMPromotedFromMatterSurface :
      Bool

    physicalCKMPromotedFromMatterSurfaceIsFalse :
      physicalCKMPromotedFromMatterSurface ≡ false

    wiringBoundary :
      List String

open MatterCarrierYukawaCKMWiringReceipt public

canonicalMatterCarrierYukawaCKMWiringReceipt :
  MatterCarrierYukawaCKMWiringReceipt
canonicalMatterCarrierYukawaCKMWiringReceipt =
  record
    { matterReceipt =
        canonicalMatterRepresentationReceiptSurface
    ; leftQuarkMatterRepresentation =
        canonicalLeftQuarkDoubletFamilyMatterRepresentation
    ; leftQuarkMatterRepresentationIsCanonical =
        refl
    ; rightUpMatterRepresentation =
        canonicalRightUpQuarkFamilyMatterRepresentation
    ; rightUpMatterRepresentationIsCanonical =
        refl
    ; rightDownMatterRepresentation =
        canonicalRightDownQuarkFamilyMatterRepresentation
    ; rightDownMatterRepresentationIsCanonical =
        refl
    ; higgsMatterRepresentation =
        canonicalHiggsDoubletMatterRepresentation
    ; higgsMatterRepresentationIsCanonical =
        refl
    ; threeGenerationStructure =
        canonicalThreeGenerationStructure
    ; threeGenerationStructureIsCanonical =
        refl
    ; carrierCKMMatrix =
        identityMixingMatrix
    ; carrierCKMMatrixIsIdentity =
        refl
    ; carrierYukawaMatrixTarget =
        MixingMatrix
    ; carrierYukawaMatrixTargetIsMixingMatrix =
        refl
    ; blockers =
        canonicalMatterYukawaCKMWiringBlockers
    ; blockersAreCanonical =
        refl
    ; firstBlocker =
        missingAbsoluteHiggsVEVW4Calibration
    ; firstBlockerIsAbsoluteHiggsVEVW4 =
        refl
    ; absoluteHiggsVEVW4Calibrated =
        false
    ; absoluteHiggsVEVW4CalibratedIsFalse =
        refl
    ; splittingFieldEigenbasisConstructed =
        false
    ; splittingFieldEigenbasisConstructedIsFalse =
        refl
    ; physicalCKMPromotedFromMatterSurface =
        false
    ; physicalCKMPromotedFromMatterSurfaceIsFalse =
        refl
    ; wiringBoundary =
        "Matter side supplies the canonical left-quark, right-up, right-down, Higgs, and three-generation constructors"
        ∷ "The carrier CKM socket is the concrete identity MixingMatrix used by the exact carrier-derived CKM lane"
        ∷ "Physical CKM/Yukawa promotion remains blocked by absolute Higgs/VEV/W4 calibration and splitting-field/eigenbasis gaps"
        ∷ []
    }

matterCarrierYukawaCKMWiringKeepsCalibrationClosed :
  absoluteHiggsVEVW4Calibrated
    canonicalMatterCarrierYukawaCKMWiringReceipt
  ≡
  false
matterCarrierYukawaCKMWiringKeepsCalibrationClosed =
  refl
