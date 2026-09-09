module DASHI.Interop.SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.BalancedTritBitFibre as Bits
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as Base369
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369MonsterFineCarrierEquivarianceAuditExact as MonsterAudit

data WikibaseSnakMeaning : Set where
  noValueMeaning : WikibaseSnakMeaning
  someValueMeaning : WikibaseSnakMeaning
  concreteValueMeaning : WikibaseSnakMeaning

data SnakTritOrientation : Set where
  epistemicCentred : SnakTritOrientation
  absenceCentred : SnakTritOrientation

encodeSnakTrit : SnakTritOrientation → WikibaseSnakMeaning → Trit.Trit
encodeSnakTrit epistemicCentred noValueMeaning = Trit.neg
encodeSnakTrit epistemicCentred someValueMeaning = Trit.zer
encodeSnakTrit epistemicCentred concreteValueMeaning = Trit.pos
encodeSnakTrit absenceCentred noValueMeaning = Trit.zer
encodeSnakTrit absenceCentred someValueMeaning = Trit.neg
encodeSnakTrit absenceCentred concreteValueMeaning = Trit.pos

decodeSnakTrit : SnakTritOrientation → Trit.Trit → WikibaseSnakMeaning
decodeSnakTrit epistemicCentred Trit.neg = noValueMeaning
decodeSnakTrit epistemicCentred Trit.zer = someValueMeaning
decodeSnakTrit epistemicCentred Trit.pos = concreteValueMeaning
decodeSnakTrit absenceCentred Trit.neg = someValueMeaning
decodeSnakTrit absenceCentred Trit.zer = noValueMeaning
decodeSnakTrit absenceCentred Trit.pos = concreteValueMeaning

snakTritRoundTrip :
  (orientation : SnakTritOrientation) →
  (meaning : WikibaseSnakMeaning) →
  decodeSnakTrit orientation (encodeSnakTrit orientation meaning) ≡ meaning
snakTritRoundTrip epistemicCentred noValueMeaning = refl
snakTritRoundTrip epistemicCentred someValueMeaning = refl
snakTritRoundTrip epistemicCentred concreteValueMeaning = refl
snakTritRoundTrip absenceCentred noValueMeaning = refl
snakTritRoundTrip absenceCentred someValueMeaning = refl
snakTritRoundTrip absenceCentred concreteValueMeaning = refl

tritSnakRoundTrip :
  (orientation : SnakTritOrientation) →
  (trit : Trit.Trit) →
  encodeSnakTrit orientation (decodeSnakTrit orientation trit) ≡ trit
tritSnakRoundTrip epistemicCentred Trit.neg = refl
tritSnakRoundTrip epistemicCentred Trit.zer = refl
tritSnakRoundTrip epistemicCentred Trit.pos = refl
tritSnakRoundTrip absenceCentred Trit.neg = refl
tritSnakRoundTrip absenceCentred Trit.zer = refl
tritSnakRoundTrip absenceCentred Trit.pos = refl

data UnbalancedSnakDigit : Set where
  digit1 digit2 digit3 : UnbalancedSnakDigit

encodeUnbalancedSnak : WikibaseSnakMeaning → UnbalancedSnakDigit
encodeUnbalancedSnak noValueMeaning = digit1
encodeUnbalancedSnak someValueMeaning = digit2
encodeUnbalancedSnak concreteValueMeaning = digit3

decodeUnbalancedSnak : UnbalancedSnakDigit → WikibaseSnakMeaning
decodeUnbalancedSnak digit1 = noValueMeaning
decodeUnbalancedSnak digit2 = someValueMeaning
decodeUnbalancedSnak digit3 = concreteValueMeaning

unbalancedSnakRoundTrip :
  (meaning : WikibaseSnakMeaning) →
  decodeUnbalancedSnak (encodeUnbalancedSnak meaning) ≡ meaning
unbalancedSnakRoundTrip noValueMeaning = refl
unbalancedSnakRoundTrip someValueMeaning = refl
unbalancedSnakRoundTrip concreteValueMeaning = refl

snakBitView :
  SnakTritOrientation → WikibaseSnakMeaning → Bits.BitStreamView
snakBitView orientation meaning = Bits.bitStreamView (encodeSnakTrit orientation meaning)

data AdmissibilityState : Set where
  rejected : AdmissibilityState
  open : AdmissibilityState
  admitted : AdmissibilityState

admissibilityTrit : AdmissibilityState → Trit.Trit
admissibilityTrit rejected = Trit.neg
admissibilityTrit open = Trit.zer
admissibilityTrit admitted = Trit.pos

tritAdmissibility : Trit.Trit → AdmissibilityState
tritAdmissibility Trit.neg = rejected
tritAdmissibility Trit.zer = open
tritAdmissibility Trit.pos = admitted

admissibilityRoundTrip :
  (state : AdmissibilityState) →
  tritAdmissibility (admissibilityTrit state) ≡ state
admissibilityRoundTrip rejected = refl
admissibilityRoundTrip open = refl
admissibilityRoundTrip admitted = refl

record NDimAdmissibilityFibre : Set₁ where
  constructor ndimAdmissibilityFibre
  field
    Axis : Set
    axisReference : Axis → String
    coordinateState : Axis → AdmissibilityState
    fibreReference : String
open NDimAdmissibilityFibre public

balancedCoordinate :
  (fibre : NDimAdmissibilityFibre) →
  Axis fibre → Trit.Trit
balancedCoordinate fibre axis = admissibilityTrit (coordinateState fibre axis)

record AdmissibilityBraid (fibre : NDimAdmissibilityFibre) : Set₁ where
  constructor admissibilityBraid
  field
    Stage : Set
    stageReference : Stage → String
    stateAt : Stage → Axis fibre → AdmissibilityState
    braidReference : String
open AdmissibilityBraid public

record FibreComplexityProfile (fibre : NDimAdmissibilityFibre) : Set₁ where
  constructor fibreComplexityProfile
  field
    CostAxis : Set
    costAxisReference : CostAxis → String
    coordinateCost : CostAxis → Axis fibre → Nat
    profileReference : String
open FibreComplexityProfile public

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

nineTritNominalStateCount : Nat
nineTritNominalStateCount = pow3 9

nineTritNominalStateCountIs19683 : nineTritNominalStateCount ≡ 19683
nineTritNominalStateCountIs19683 = refl

data NatNineAxis : Set where
  subjectIdentityAxis : NatNineAxis
  transportAxis : NatNineAxis
  nativeFamilyCoverageAxis : NatNineAxis
  rankVisibilityAxis : NatNineAxis
  qualifierConstraintAxis : NatNineAxis
  propertyScopeAxis : NatNineAxis
  sourceSupportAxis : NatNineAxis
  authorityAxis : NatNineAxis
  semanticCorrespondenceAxis : NatNineAxis

record NatNineAxisState : Set where
  constructor natNineAxisState
  field
    subjectIdentity : SSP.SSPTrit
    transport : SSP.SSPTrit
    nativeFamilyCoverage : SSP.SSPTrit
    rankVisibility : SSP.SSPTrit
    qualifierConstraint : SSP.SSPTrit
    propertyScope : SSP.SSPTrit
    sourceSupport : SSP.SSPTrit
    authority : SSP.SSPTrit
    semanticCorrespondence : SSP.SSPTrit
open NatNineAxisState public

toBase369NineTrits : NatNineAxisState → Base369.NineTrits
toBase369NineTrits
  (natNineAxisState a b c d e f g h i) =
  Base369.nineTrits a b c d e f g h i

fromBase369NineTrits : Base369.NineTrits → NatNineAxisState
fromBase369NineTrits
  (Base369.nineTrits a b c d e f g h i) =
  natNineAxisState a b c d e f g h i

natBase369RoundTrip :
  (state : NatNineAxisState) →
  fromBase369NineTrits (toBase369NineTrits state) ≡ state
natBase369RoundTrip (natNineAxisState a b c d e f g h i) = refl

base369NatRoundTrip :
  (state : Base369.NineTrits) →
  toBase369NineTrits (fromBase369NineTrits state) ≡ state
base369NatRoundTrip (Base369.nineTrits a b c d e f g h i) = refl

natNineAxisToHyperformal : NatNineAxisState → Geometry.TernaryHyperformalPoint
natNineAxisToHyperformal state =
  Geometry.nineTritsToFabric (toBase369NineTrits state)

record WikidataTernaryAdmissibilityBoundary : Set where
  constructor wikidataTernaryAdmissibilityBoundary
  field
    wikibaseSnakTripleHasExactBalancedCodec : Bool
    balancedCodecIsWikibaseTruthSemantics : Bool
    zeroTritMeansBooleanFalse : Bool
    binarySupportBitMeansSemanticFalse : Bool
    openResidualIsThirdAdmissibilityState : Bool
    arbitraryAxisFamilySupported : Bool
    nineAxisProjectionUsesExistingBase369Carrier : Bool
    nineAxisNominalStateCountIs19683 : Bool
    sameCarrierCreatesMonsterAction : Bool
    monsterEquivarianceNeedsSeparateReceipt : Bool

canonicalWikidataTernaryAdmissibilityBoundary :
  WikidataTernaryAdmissibilityBoundary
canonicalWikidataTernaryAdmissibilityBoundary =
  wikidataTernaryAdmissibilityBoundary
    true false false false true true true true false true

monsterBoundaryRetained : MonsterAudit.FineCarrierBidiBoundary
monsterBoundaryRetained = MonsterAudit.canonicalFineCarrierBidiBoundary
