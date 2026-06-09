module DASHI.Physics.Moonshine.DongLiMasonOrbifoldReceiptSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Dong-Li-Mason orbifold receipt surface.
--
-- The concrete table below is a receipt surface for later composition.  The
-- external mathematics is represented by postulated authority receipts:
-- Ogg for the supersingular-prime list, no-ghost for the physical-state
-- bridge, and Dong-Li-Mason for the orbifold Lie-algebra outcomes.

data MoonshineAuthorityCitation : Set where
  oggSupersingularPrimeCitation :
    MoonshineAuthorityCitation
  noGhostTheoremCitation :
    MoonshineAuthorityCitation
  dongLiMasonOrbifoldCitation :
    MoonshineAuthorityCitation

record MoonshineAuthorityReceipt : Set where
  field
    citation :
      MoonshineAuthorityCitation
    authorityLabel :
      String
    acceptedAsExternalAuthority :
      Bool
    acceptedAsExternalAuthorityIsTrue :
      acceptedAsExternalAuthority ≡ true

postulate
  oggSupersingularPrimeAuthority :
    MoonshineAuthorityReceipt

  noGhostPhysicalStateAuthority :
    MoonshineAuthorityReceipt

  dongLiMasonOrbifoldAuthority :
    MoonshineAuthorityReceipt

data SupersingularPrime : Set where
  ss2 :
    SupersingularPrime
  ss3 :
    SupersingularPrime
  ss5 :
    SupersingularPrime
  ss7 :
    SupersingularPrime
  ss11 :
    SupersingularPrime
  ss13 :
    SupersingularPrime
  ss17 :
    SupersingularPrime
  ss19 :
    SupersingularPrime
  ss23 :
    SupersingularPrime
  ss29 :
    SupersingularPrime
  ss31 :
    SupersingularPrime
  ss41 :
    SupersingularPrime
  ss47 :
    SupersingularPrime
  ss59 :
    SupersingularPrime
  ss71 :
    SupersingularPrime

supersingularPrimeNat :
  SupersingularPrime →
  Nat
supersingularPrimeNat ss2 =
  2
supersingularPrimeNat ss3 =
  3
supersingularPrimeNat ss5 =
  5
supersingularPrimeNat ss7 =
  7
supersingularPrimeNat ss11 =
  11
supersingularPrimeNat ss13 =
  13
supersingularPrimeNat ss17 =
  17
supersingularPrimeNat ss19 =
  19
supersingularPrimeNat ss23 =
  23
supersingularPrimeNat ss29 =
  29
supersingularPrimeNat ss31 =
  31
supersingularPrimeNat ss41 =
  41
supersingularPrimeNat ss47 =
  47
supersingularPrimeNat ss59 =
  59
supersingularPrimeNat ss71 =
  71

allSupersingularPrimes :
  List SupersingularPrime
allSupersingularPrimes =
  ss2
  ∷ ss3
  ∷ ss5
  ∷ ss7
  ∷ ss11
  ∷ ss13
  ∷ ss17
  ∷ ss19
  ∷ ss23
  ∷ ss29
  ∷ ss31
  ∷ ss41
  ∷ ss47
  ∷ ss59
  ∷ ss71
  ∷ []

supersingularPrimeCount :
  Nat
supersingularPrimeCount =
  15

data OrbifoldLieAlgebraOutcome : Set where
  zeroU1 :
    OrbifoldLieAlgebraOutcome
  su2 :
    OrbifoldLieAlgebraOutcome
  su3 :
    OrbifoldLieAlgebraOutcome
  zeroTrivial :
    OrbifoldLieAlgebraOutcome

orbifoldOutcomeForPrime :
  SupersingularPrime →
  OrbifoldLieAlgebraOutcome
orbifoldOutcomeForPrime ss2 =
  zeroU1
orbifoldOutcomeForPrime ss3 =
  su2
orbifoldOutcomeForPrime ss5 =
  su3
orbifoldOutcomeForPrime ss7 =
  su2
orbifoldOutcomeForPrime ss11 =
  zeroTrivial
orbifoldOutcomeForPrime ss13 =
  zeroTrivial
orbifoldOutcomeForPrime ss17 =
  zeroTrivial
orbifoldOutcomeForPrime ss19 =
  zeroTrivial
orbifoldOutcomeForPrime ss23 =
  zeroTrivial
orbifoldOutcomeForPrime ss29 =
  zeroTrivial
orbifoldOutcomeForPrime ss31 =
  zeroTrivial
orbifoldOutcomeForPrime ss41 =
  zeroTrivial
orbifoldOutcomeForPrime ss47 =
  zeroTrivial
orbifoldOutcomeForPrime ss59 =
  zeroTrivial
orbifoldOutcomeForPrime ss71 =
  zeroTrivial

laneDimensionForPrime :
  SupersingularPrime →
  Nat
laneDimensionForPrime ss2 =
  1
laneDimensionForPrime ss3 =
  2
laneDimensionForPrime ss5 =
  3
laneDimensionForPrime ss7 =
  2
laneDimensionForPrime ss11 =
  0
laneDimensionForPrime ss13 =
  0
laneDimensionForPrime ss17 =
  0
laneDimensionForPrime ss19 =
  0
laneDimensionForPrime ss23 =
  0
laneDimensionForPrime ss29 =
  0
laneDimensionForPrime ss31 =
  0
laneDimensionForPrime ss41 =
  0
laneDimensionForPrime ss47 =
  0
laneDimensionForPrime ss59 =
  0
laneDimensionForPrime ss71 =
  0

weightOneLieAlgebraDimensionForPrime :
  SupersingularPrime →
  Nat
weightOneLieAlgebraDimensionForPrime ss2 =
  0
weightOneLieAlgebraDimensionForPrime ss3 =
  3
weightOneLieAlgebraDimensionForPrime ss5 =
  8
weightOneLieAlgebraDimensionForPrime ss7 =
  3
weightOneLieAlgebraDimensionForPrime ss11 =
  0
weightOneLieAlgebraDimensionForPrime ss13 =
  0
weightOneLieAlgebraDimensionForPrime ss17 =
  0
weightOneLieAlgebraDimensionForPrime ss19 =
  0
weightOneLieAlgebraDimensionForPrime ss23 =
  0
weightOneLieAlgebraDimensionForPrime ss29 =
  0
weightOneLieAlgebraDimensionForPrime ss31 =
  0
weightOneLieAlgebraDimensionForPrime ss41 =
  0
weightOneLieAlgebraDimensionForPrime ss47 =
  0
weightOneLieAlgebraDimensionForPrime ss59 =
  0
weightOneLieAlgebraDimensionForPrime ss71 =
  0

weightOneLieAlgebraRankForPrime :
  SupersingularPrime →
  Nat
weightOneLieAlgebraRankForPrime ss2 =
  0
weightOneLieAlgebraRankForPrime ss3 =
  1
weightOneLieAlgebraRankForPrime ss5 =
  2
weightOneLieAlgebraRankForPrime ss7 =
  1
weightOneLieAlgebraRankForPrime ss11 =
  0
weightOneLieAlgebraRankForPrime ss13 =
  0
weightOneLieAlgebraRankForPrime ss17 =
  0
weightOneLieAlgebraRankForPrime ss19 =
  0
weightOneLieAlgebraRankForPrime ss23 =
  0
weightOneLieAlgebraRankForPrime ss29 =
  0
weightOneLieAlgebraRankForPrime ss31 =
  0
weightOneLieAlgebraRankForPrime ss41 =
  0
weightOneLieAlgebraRankForPrime ss47 =
  0
weightOneLieAlgebraRankForPrime ss59 =
  0
weightOneLieAlgebraRankForPrime ss71 =
  0

isPositiveLane :
  SupersingularPrime →
  Bool
isPositiveLane ss2 =
  true
isPositiveLane ss3 =
  true
isPositiveLane ss5 =
  true
isPositiveLane ss7 =
  true
isPositiveLane ss11 =
  false
isPositiveLane ss13 =
  false
isPositiveLane ss17 =
  false
isPositiveLane ss19 =
  false
isPositiveLane ss23 =
  false
isPositiveLane ss29 =
  false
isPositiveLane ss31 =
  false
isPositiveLane ss41 =
  false
isPositiveLane ss47 =
  false
isPositiveLane ss59 =
  false
isPositiveLane ss71 =
  false

isZeroOrTrivialLane :
  SupersingularPrime →
  Bool
isZeroOrTrivialLane ss2 =
  true
isZeroOrTrivialLane ss3 =
  false
isZeroOrTrivialLane ss5 =
  false
isZeroOrTrivialLane ss7 =
  false
isZeroOrTrivialLane ss11 =
  true
isZeroOrTrivialLane ss13 =
  true
isZeroOrTrivialLane ss17 =
  true
isZeroOrTrivialLane ss19 =
  true
isZeroOrTrivialLane ss23 =
  true
isZeroOrTrivialLane ss29 =
  true
isZeroOrTrivialLane ss31 =
  true
isZeroOrTrivialLane ss41 =
  true
isZeroOrTrivialLane ss47 =
  true
isZeroOrTrivialLane ss59 =
  true
isZeroOrTrivialLane ss71 =
  true

data LargeSupersingularPrime : Set where
  large11 :
    LargeSupersingularPrime
  large13 :
    LargeSupersingularPrime
  large17 :
    LargeSupersingularPrime
  large19 :
    LargeSupersingularPrime
  large23 :
    LargeSupersingularPrime
  large29 :
    LargeSupersingularPrime
  large31 :
    LargeSupersingularPrime
  large41 :
    LargeSupersingularPrime
  large47 :
    LargeSupersingularPrime
  large59 :
    LargeSupersingularPrime
  large71 :
    LargeSupersingularPrime

largeSupersingularPrime :
  LargeSupersingularPrime →
  SupersingularPrime
largeSupersingularPrime large11 =
  ss11
largeSupersingularPrime large13 =
  ss13
largeSupersingularPrime large17 =
  ss17
largeSupersingularPrime large19 =
  ss19
largeSupersingularPrime large23 =
  ss23
largeSupersingularPrime large29 =
  ss29
largeSupersingularPrime large31 =
  ss31
largeSupersingularPrime large41 =
  ss41
largeSupersingularPrime large47 =
  ss47
largeSupersingularPrime large59 =
  ss59
largeSupersingularPrime large71 =
  ss71

largePrimeOutcomeIsZeroTrivial :
  (p : LargeSupersingularPrime) →
  orbifoldOutcomeForPrime (largeSupersingularPrime p) ≡ zeroTrivial
largePrimeOutcomeIsZeroTrivial large11 =
  refl
largePrimeOutcomeIsZeroTrivial large13 =
  refl
largePrimeOutcomeIsZeroTrivial large17 =
  refl
largePrimeOutcomeIsZeroTrivial large19 =
  refl
largePrimeOutcomeIsZeroTrivial large23 =
  refl
largePrimeOutcomeIsZeroTrivial large29 =
  refl
largePrimeOutcomeIsZeroTrivial large31 =
  refl
largePrimeOutcomeIsZeroTrivial large41 =
  refl
largePrimeOutcomeIsZeroTrivial large47 =
  refl
largePrimeOutcomeIsZeroTrivial large59 =
  refl
largePrimeOutcomeIsZeroTrivial large71 =
  refl

largePrimeLaneDimensionIsZero :
  (p : LargeSupersingularPrime) →
  laneDimensionForPrime (largeSupersingularPrime p) ≡ zero
largePrimeLaneDimensionIsZero large11 =
  refl
largePrimeLaneDimensionIsZero large13 =
  refl
largePrimeLaneDimensionIsZero large17 =
  refl
largePrimeLaneDimensionIsZero large19 =
  refl
largePrimeLaneDimensionIsZero large23 =
  refl
largePrimeLaneDimensionIsZero large29 =
  refl
largePrimeLaneDimensionIsZero large31 =
  refl
largePrimeLaneDimensionIsZero large41 =
  refl
largePrimeLaneDimensionIsZero large47 =
  refl
largePrimeLaneDimensionIsZero large59 =
  refl
largePrimeLaneDimensionIsZero large71 =
  refl

record WeightOneOrbifoldLieAlgebraReceipt : Set where
  field
    prime :
      SupersingularPrime
    primeValue :
      Nat
    primeValueMatchesTag :
      primeValue ≡ supersingularPrimeNat prime
    outcome :
      OrbifoldLieAlgebraOutcome
    outcomeMatchesPrime :
      outcome ≡ orbifoldOutcomeForPrime prime
    laneDimension :
      Nat
    laneDimensionMatchesPrime :
      laneDimension ≡ laneDimensionForPrime prime
    weightOneLieAlgebraDimension :
      Nat
    weightOneLieAlgebraDimensionMatchesPrime :
      weightOneLieAlgebraDimension
      ≡
      weightOneLieAlgebraDimensionForPrime prime
    weightOneLieAlgebraRank :
      Nat
    weightOneLieAlgebraRankMatchesPrime :
      weightOneLieAlgebraRank
      ≡
      weightOneLieAlgebraRankForPrime prime
    positiveLane :
      Bool
    positiveLaneMatchesPrime :
      positiveLane ≡ isPositiveLane prime
    zeroOrTrivialLane :
      Bool
    zeroOrTrivialLaneMatchesPrime :
      zeroOrTrivialLane ≡ isZeroOrTrivialLane prime
    citedAuthorities :
      List MoonshineAuthorityReceipt

mkWeightOneReceipt :
  (p : SupersingularPrime) →
  WeightOneOrbifoldLieAlgebraReceipt
mkWeightOneReceipt p =
  record
    { prime =
        p
    ; primeValue =
        supersingularPrimeNat p
    ; primeValueMatchesTag =
        refl
    ; outcome =
        orbifoldOutcomeForPrime p
    ; outcomeMatchesPrime =
        refl
    ; laneDimension =
        laneDimensionForPrime p
    ; laneDimensionMatchesPrime =
        refl
    ; weightOneLieAlgebraDimension =
        weightOneLieAlgebraDimensionForPrime p
    ; weightOneLieAlgebraDimensionMatchesPrime =
        refl
    ; weightOneLieAlgebraRank =
        weightOneLieAlgebraRankForPrime p
    ; weightOneLieAlgebraRankMatchesPrime =
        refl
    ; positiveLane =
        isPositiveLane p
    ; positiveLaneMatchesPrime =
        refl
    ; zeroOrTrivialLane =
        isZeroOrTrivialLane p
    ; zeroOrTrivialLaneMatchesPrime =
        refl
    ; citedAuthorities =
        oggSupersingularPrimeAuthority
        ∷ noGhostPhysicalStateAuthority
        ∷ dongLiMasonOrbifoldAuthority
        ∷ []
    }

p2OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p2OrbifoldReceipt =
  mkWeightOneReceipt ss2

p3OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p3OrbifoldReceipt =
  mkWeightOneReceipt ss3

p5OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p5OrbifoldReceipt =
  mkWeightOneReceipt ss5

p7OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p7OrbifoldReceipt =
  mkWeightOneReceipt ss7

p11OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p11OrbifoldReceipt =
  mkWeightOneReceipt ss11

p13OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p13OrbifoldReceipt =
  mkWeightOneReceipt ss13

p17OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p17OrbifoldReceipt =
  mkWeightOneReceipt ss17

p19OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p19OrbifoldReceipt =
  mkWeightOneReceipt ss19

p23OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p23OrbifoldReceipt =
  mkWeightOneReceipt ss23

p29OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p29OrbifoldReceipt =
  mkWeightOneReceipt ss29

p31OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p31OrbifoldReceipt =
  mkWeightOneReceipt ss31

p41OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p41OrbifoldReceipt =
  mkWeightOneReceipt ss41

p47OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p47OrbifoldReceipt =
  mkWeightOneReceipt ss47

p59OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p59OrbifoldReceipt =
  mkWeightOneReceipt ss59

p71OrbifoldReceipt :
  WeightOneOrbifoldLieAlgebraReceipt
p71OrbifoldReceipt =
  mkWeightOneReceipt ss71

allWeightOneOrbifoldReceipts :
  List WeightOneOrbifoldLieAlgebraReceipt
allWeightOneOrbifoldReceipts =
  p2OrbifoldReceipt
  ∷ p3OrbifoldReceipt
  ∷ p5OrbifoldReceipt
  ∷ p7OrbifoldReceipt
  ∷ p11OrbifoldReceipt
  ∷ p13OrbifoldReceipt
  ∷ p17OrbifoldReceipt
  ∷ p19OrbifoldReceipt
  ∷ p23OrbifoldReceipt
  ∷ p29OrbifoldReceipt
  ∷ p31OrbifoldReceipt
  ∷ p41OrbifoldReceipt
  ∷ p47OrbifoldReceipt
  ∷ p59OrbifoldReceipt
  ∷ p71OrbifoldReceipt
  ∷ []

p2OutcomeIsZeroU1 :
  orbifoldOutcomeForPrime ss2 ≡ zeroU1
p2OutcomeIsZeroU1 =
  refl

p2LaneDimensionIsOne :
  laneDimensionForPrime ss2 ≡ 1
p2LaneDimensionIsOne =
  refl

p3OutcomeIsSu2 :
  orbifoldOutcomeForPrime ss3 ≡ su2
p3OutcomeIsSu2 =
  refl

p3LaneDimensionIsTwo :
  laneDimensionForPrime ss3 ≡ 2
p3LaneDimensionIsTwo =
  refl

p5OutcomeIsSu3 :
  orbifoldOutcomeForPrime ss5 ≡ su3
p5OutcomeIsSu3 =
  refl

p5LaneDimensionIsThree :
  laneDimensionForPrime ss5 ≡ 3
p5LaneDimensionIsThree =
  refl

p7OutcomeIsSu2 :
  orbifoldOutcomeForPrime ss7 ≡ su2
p7OutcomeIsSu2 =
  refl

p7LaneDimensionIsTwo :
  laneDimensionForPrime ss7 ≡ 2
p7LaneDimensionIsTwo =
  refl

record DongLiMasonOrbifoldReceiptSurface : Set where
  field
    authorityReceipts :
      List MoonshineAuthorityReceipt
    supersingularPrimes :
      List SupersingularPrime
    tablePrimeCount :
      Nat
    tablePrimeCountIsFifteen :
      tablePrimeCount ≡ 15
    weightOneReceipts :
      List WeightOneOrbifoldLieAlgebraReceipt
    p2Receipt :
      WeightOneOrbifoldLieAlgebraReceipt
    p3Receipt :
      WeightOneOrbifoldLieAlgebraReceipt
    p5Receipt :
      WeightOneOrbifoldLieAlgebraReceipt
    p7Receipt :
      WeightOneOrbifoldLieAlgebraReceipt
    laterCompositionReady :
      Bool
    laterCompositionReadyIsTrue :
      laterCompositionReady ≡ true
    authoritySurfaceOnly :
      Bool
    authoritySurfaceOnlyIsTrue :
      authoritySurfaceOnly ≡ true

canonicalDongLiMasonOrbifoldReceiptSurface :
  DongLiMasonOrbifoldReceiptSurface
canonicalDongLiMasonOrbifoldReceiptSurface =
  record
    { authorityReceipts =
        oggSupersingularPrimeAuthority
        ∷ noGhostPhysicalStateAuthority
        ∷ dongLiMasonOrbifoldAuthority
        ∷ []
    ; supersingularPrimes =
        allSupersingularPrimes
    ; tablePrimeCount =
        supersingularPrimeCount
    ; tablePrimeCountIsFifteen =
        refl
    ; weightOneReceipts =
        allWeightOneOrbifoldReceipts
    ; p2Receipt =
        p2OrbifoldReceipt
    ; p3Receipt =
        p3OrbifoldReceipt
    ; p5Receipt =
        p5OrbifoldReceipt
    ; p7Receipt =
        p7OrbifoldReceipt
    ; laterCompositionReady =
        true
    ; laterCompositionReadyIsTrue =
        refl
    ; authoritySurfaceOnly =
        true
    ; authoritySurfaceOnlyIsTrue =
        refl
    }

canonicalSurfaceCompositionReady :
  DongLiMasonOrbifoldReceiptSurface.laterCompositionReady
    canonicalDongLiMasonOrbifoldReceiptSurface
  ≡ true
canonicalSurfaceCompositionReady =
  refl

canonicalSurfaceIsAuthoritySurfaceOnly :
  DongLiMasonOrbifoldReceiptSurface.authoritySurfaceOnly
    canonicalDongLiMasonOrbifoldReceiptSurface
  ≡ true
canonicalSurfaceIsAuthoritySurfaceOnly =
  refl
