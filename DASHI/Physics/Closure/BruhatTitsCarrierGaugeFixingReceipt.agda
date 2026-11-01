module DASHI.Physics.Closure.BruhatTitsCarrierGaugeFixingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.SupersingularPrimeLaneBridge as SSP

------------------------------------------------------------------------
-- Bruhat-Tits carrier gauge-fixing receipt.
--
-- This receipt records the non-Archimedean carrier picture only.  Each SSP
-- prime lane has a Bruhat-Tits tree concept with valency p+1 as data.  The
-- tree base is contractible, so this carrier has no principal-bundle
-- obstruction to choosing a representative.  Singer's continuum theorem is
-- recorded as non-applicable because the base here is a non-Archimedean tree,
-- not a compact smooth continuum manifold.
--
-- The quotient is the carrier quotient by depth/N per prime.  The product
-- carrier is recorded conceptually as N^15 over the SSP prime list.  Phase
-- lives on edges, while FactorVec/depth is vertex/amplitude data.  Unique
-- paths in trees give the geometric basis for a unique representative.  The
-- continuum Gribov problem remains outside this carrier; Gate3 must preserve
-- or handle the lift before any continuum claim.
-- The braid/KP correction is fail-closed here too: this BT carrier receipt
-- does not construct a Yang-Baxter theorem or a KP theorem.

data GaugeFixingReceiptStatus : Set where
  bruhatTitsCarrierGaugeFixingRecordedNoContinuumPromotion :
    GaugeFixingReceiptStatus

data BruhatTitsTreeConcept : Set where
  bruhatTitsTreePerSSPPrime :
    BruhatTitsTreeConcept

data TreeValencyConcept : Set where
  valencyPPlusOnePerPrime :
    TreeValencyConcept

data CarrierContractibilityConcept : Set where
  treeBaseContractible :
    CarrierContractibilityConcept

data PrincipalBundleObstructionStatus : Set where
  noPrincipalBundleObstructionOnContractibleTreeBase :
    PrincipalBundleObstructionStatus

data SingerApplicabilityStatus : Set where
  singerTheoremNotApplicableToNonArchimedeanTreeBase :
    SingerApplicabilityStatus

data GaugeOrbitQuotientConcept : Set where
  depthModuloNPerPrime :
    GaugeOrbitQuotientConcept

data ProductCarrierConcept : Set where
  naturalDepthProductOverFifteenSSPPrimes :
    ProductCarrierConcept

data CarrierCoordinateRole : Set where
  phaseActsOnEdges :
    CarrierCoordinateRole

  factorVecDepthIsVertexAmplitude :
    CarrierCoordinateRole

canonicalCarrierCoordinateRoles :
  List CarrierCoordinateRole
canonicalCarrierCoordinateRoles =
  phaseActsOnEdges
  ∷ factorVecDepthIsVertexAmplitude
  ∷ []

data PathUniquenessConcept : Set where
  uniqueTreePathGivesUniqueRepresentativeBasis :
    PathUniquenessConcept

data ContinuumBoundaryStatus : Set where
  continuumGribovOutsideCarrierGate3MustPreserveOrHandleLift :
    ContinuumBoundaryStatus

data SSPPrimeLaneValency : Set where
  p2Valency3 :
    SSPPrimeLaneValency

  p3Valency4 :
    SSPPrimeLaneValency

  p5Valency6 :
    SSPPrimeLaneValency

  p7Valency8 :
    SSPPrimeLaneValency

  p11Valency12 :
    SSPPrimeLaneValency

  p13Valency14 :
    SSPPrimeLaneValency

  p17Valency18 :
    SSPPrimeLaneValency

  p19Valency20 :
    SSPPrimeLaneValency

  p23Valency24 :
    SSPPrimeLaneValency

  p29Valency30 :
    SSPPrimeLaneValency

  p31Valency32 :
    SSPPrimeLaneValency

  p41Valency42 :
    SSPPrimeLaneValency

  p47Valency48 :
    SSPPrimeLaneValency

  p59Valency60 :
    SSPPrimeLaneValency

  p71Valency72 :
    SSPPrimeLaneValency

canonicalSSPPrimeLaneValencies :
  List SSPPrimeLaneValency
canonicalSSPPrimeLaneValencies =
  p2Valency3
  ∷ p3Valency4
  ∷ p5Valency6
  ∷ p7Valency8
  ∷ p11Valency12
  ∷ p13Valency14
  ∷ p17Valency18
  ∷ p19Valency20
  ∷ p23Valency24
  ∷ p29Valency30
  ∷ p31Valency32
  ∷ p41Valency42
  ∷ p47Valency48
  ∷ p59Valency60
  ∷ p71Valency72
  ∷ []

data CarrierGaugeFixingBoundary : Set where
  carrierSideOnly :
    CarrierGaugeFixingBoundary

  noContinuumGaugeSliceConstructed :
    CarrierGaugeFixingBoundary

  noSingerTheoremInvocation :
    CarrierGaugeFixingBoundary

  noContinuumGribovDischarge :
    CarrierGaugeFixingBoundary

  noGate3Proof :
    CarrierGaugeFixingBoundary

  noClayPromotion :
    CarrierGaugeFixingBoundary

  noYangBaxterTheoremPromotion :
    CarrierGaugeFixingBoundary

  noKPTheoremPromotion :
    CarrierGaugeFixingBoundary

canonicalCarrierGaugeFixingBoundaries :
  List CarrierGaugeFixingBoundary
canonicalCarrierGaugeFixingBoundaries =
  carrierSideOnly
  ∷ noContinuumGaugeSliceConstructed
  ∷ noSingerTheoremInvocation
  ∷ noContinuumGribovDischarge
  ∷ noGate3Proof
  ∷ noClayPromotion
  ∷ noYangBaxterTheoremPromotion
  ∷ noKPTheoremPromotion
  ∷ []

data ContinuumPromotion : Set where
data Gate3Promotion : Set where
data ClayPromotion : Set where

continuumPromotionImpossibleHere :
  ContinuumPromotion →
  ⊥
continuumPromotionImpossibleHere ()

gate3PromotionImpossibleHere :
  Gate3Promotion →
  ⊥
gate3PromotionImpossibleHere ()

clayPromotionImpossibleHere :
  ClayPromotion →
  ⊥
clayPromotionImpossibleHere ()

bruhatTitsCarrierGaugeFixingSummary :
  String
bruhatTitsCarrierGaugeFixingSummary =
  "Bruhat-Tits carrier gauge fixing: one contractible tree per SSP prime, valency p+1, quotient depth/N per prime, product carrier concept N^15."

coordinateRoleSummary :
  String
coordinateRoleSummary =
  "Phase is edge data; FactorVec/depth is vertex/amplitude data."

continuumBoundarySummary :
  String
continuumBoundarySummary =
  "Continuum Gribov remains outside this carrier; Gate3 must preserve or handle the lift; no Yang-Baxter or KP theorem is promoted."

record BruhatTitsCarrierGaugeFixingReceipt : Setω where
  field
    status :
      GaugeFixingReceiptStatus

    statusIsCanonical :
      status ≡
      bruhatTitsCarrierGaugeFixingRecordedNoContinuumPromotion

    sspPrimeNats :
      List Nat

    sspPrimeNatsAreCanonical :
      sspPrimeNats ≡ SSP.canonicalSupersingularPrimeLaneNats

    sspPrimeCount :
      Nat

    sspPrimeCountIsFifteen :
      sspPrimeCount ≡ 15

    treeConcept :
      BruhatTitsTreeConcept

    treeConceptIsPerSSPPrime :
      treeConcept ≡ bruhatTitsTreePerSSPPrime

    valencyConcept :
      TreeValencyConcept

    valencyConceptIsPPlusOne :
      valencyConcept ≡ valencyPPlusOnePerPrime

    primeLaneValencies :
      List SSPPrimeLaneValency

    primeLaneValenciesAreCanonical :
      primeLaneValencies ≡ canonicalSSPPrimeLaneValencies

    contractibility :
      CarrierContractibilityConcept

    contractibilityIsTreeBase :
      contractibility ≡ treeBaseContractible

    principalBundleObstruction :
      PrincipalBundleObstructionStatus

    contractibleBaseRemovesPrincipalBundleObstruction :
      principalBundleObstruction ≡
      noPrincipalBundleObstructionOnContractibleTreeBase

    singerApplicability :
      SingerApplicabilityStatus

    singerApplicabilityIsBlockedOnTreeBase :
      singerApplicability ≡
      singerTheoremNotApplicableToNonArchimedeanTreeBase

    gaugeOrbitQuotient :
      GaugeOrbitQuotientConcept

    gaugeOrbitQuotientIsDepthModuloNPerPrime :
      gaugeOrbitQuotient ≡ depthModuloNPerPrime

    productCarrier :
      ProductCarrierConcept

    productCarrierIsNaturalDepthProductOverFifteen :
      productCarrier ≡ naturalDepthProductOverFifteenSSPPrimes

    productCarrierExponent :
      Nat

    productCarrierExponentIsFifteen :
      productCarrierExponent ≡ 15

    coordinateRoles :
      List CarrierCoordinateRole

    coordinateRolesAreCanonical :
      coordinateRoles ≡ canonicalCarrierCoordinateRoles

    phaseIsEdgeData :
      Bool

    phaseIsEdgeDataIsTrue :
      phaseIsEdgeData ≡ true

    factorVecDepthIsVertexAmplitudeData :
      Bool

    factorVecDepthIsVertexAmplitudeDataIsTrue :
      factorVecDepthIsVertexAmplitudeData ≡ true

    pathUniqueness :
      PathUniquenessConcept

    pathUniquenessGivesUniqueRepresentativeBasis :
      pathUniqueness ≡
      uniqueTreePathGivesUniqueRepresentativeBasis

    uniqueRepresentativeBasisRecorded :
      Bool

    uniqueRepresentativeBasisRecordedIsTrue :
      uniqueRepresentativeBasisRecorded ≡ true

    continuumBoundary :
      ContinuumBoundaryStatus

    continuumBoundaryIsOutsideCarrierGate3Lift :
      continuumBoundary ≡
      continuumGribovOutsideCarrierGate3MustPreserveOrHandleLift

    continuumGribovDischarged :
      Bool

    continuumGribovDischargedIsFalse :
      continuumGribovDischarged ≡ false

    gate3LiftObligationPreserved :
      Bool

    gate3LiftObligationPreservedIsTrue :
      gate3LiftObligationPreserved ≡ true

    continuumGaugeSliceConstructed :
      Bool

    continuumGaugeSliceConstructedIsFalse :
      continuumGaugeSliceConstructed ≡ false

    clayPromotionMade :
      Bool

    clayPromotionMadeIsFalse :
      clayPromotionMade ≡ false

    yangBaxterTheoremPromoted :
      Bool

    yangBaxterTheoremPromotedIsFalse :
      yangBaxterTheoremPromoted ≡ false

    kpTheoremPromoted :
      Bool

    kpTheoremPromotedIsFalse :
      kpTheoremPromoted ≡ false

    boundaries :
      List CarrierGaugeFixingBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalCarrierGaugeFixingBoundaries

    noContinuumPromotion :
      ContinuumPromotion →
      ⊥

    noGate3Promotion :
      Gate3Promotion →
      ⊥

    noClayPromotionAuthority :
      ClayPromotion →
      ⊥

open BruhatTitsCarrierGaugeFixingReceipt public

canonicalBruhatTitsCarrierGaugeFixingReceipt :
  BruhatTitsCarrierGaugeFixingReceipt
canonicalBruhatTitsCarrierGaugeFixingReceipt =
  record
    { status =
        bruhatTitsCarrierGaugeFixingRecordedNoContinuumPromotion
    ; statusIsCanonical =
        refl
    ; sspPrimeNats =
        SSP.canonicalSupersingularPrimeLaneNats
    ; sspPrimeNatsAreCanonical =
        refl
    ; sspPrimeCount =
        15
    ; sspPrimeCountIsFifteen =
        refl
    ; treeConcept =
        bruhatTitsTreePerSSPPrime
    ; treeConceptIsPerSSPPrime =
        refl
    ; valencyConcept =
        valencyPPlusOnePerPrime
    ; valencyConceptIsPPlusOne =
        refl
    ; primeLaneValencies =
        canonicalSSPPrimeLaneValencies
    ; primeLaneValenciesAreCanonical =
        refl
    ; contractibility =
        treeBaseContractible
    ; contractibilityIsTreeBase =
        refl
    ; principalBundleObstruction =
        noPrincipalBundleObstructionOnContractibleTreeBase
    ; contractibleBaseRemovesPrincipalBundleObstruction =
        refl
    ; singerApplicability =
        singerTheoremNotApplicableToNonArchimedeanTreeBase
    ; singerApplicabilityIsBlockedOnTreeBase =
        refl
    ; gaugeOrbitQuotient =
        depthModuloNPerPrime
    ; gaugeOrbitQuotientIsDepthModuloNPerPrime =
        refl
    ; productCarrier =
        naturalDepthProductOverFifteenSSPPrimes
    ; productCarrierIsNaturalDepthProductOverFifteen =
        refl
    ; productCarrierExponent =
        15
    ; productCarrierExponentIsFifteen =
        refl
    ; coordinateRoles =
        canonicalCarrierCoordinateRoles
    ; coordinateRolesAreCanonical =
        refl
    ; phaseIsEdgeData =
        true
    ; phaseIsEdgeDataIsTrue =
        refl
    ; factorVecDepthIsVertexAmplitudeData =
        true
    ; factorVecDepthIsVertexAmplitudeDataIsTrue =
        refl
    ; pathUniqueness =
        uniqueTreePathGivesUniqueRepresentativeBasis
    ; pathUniquenessGivesUniqueRepresentativeBasis =
        refl
    ; uniqueRepresentativeBasisRecorded =
        true
    ; uniqueRepresentativeBasisRecordedIsTrue =
        refl
    ; continuumBoundary =
        continuumGribovOutsideCarrierGate3MustPreserveOrHandleLift
    ; continuumBoundaryIsOutsideCarrierGate3Lift =
        refl
    ; continuumGribovDischarged =
        false
    ; continuumGribovDischargedIsFalse =
        refl
    ; gate3LiftObligationPreserved =
        true
    ; gate3LiftObligationPreservedIsTrue =
        refl
    ; continuumGaugeSliceConstructed =
        false
    ; continuumGaugeSliceConstructedIsFalse =
        refl
    ; clayPromotionMade =
        false
    ; clayPromotionMadeIsFalse =
        refl
    ; yangBaxterTheoremPromoted =
        false
    ; yangBaxterTheoremPromotedIsFalse =
        refl
    ; kpTheoremPromoted =
        false
    ; kpTheoremPromotedIsFalse =
        refl
    ; boundaries =
        canonicalCarrierGaugeFixingBoundaries
    ; boundariesAreCanonical =
        refl
    ; noContinuumPromotion =
        continuumPromotionImpossibleHere
    ; noGate3Promotion =
        gate3PromotionImpossibleHere
    ; noClayPromotionAuthority =
        clayPromotionImpossibleHere
    }

canonicalBruhatTitsCarrierGaugeFixingIsCarrierOnly :
  clayPromotionMade canonicalBruhatTitsCarrierGaugeFixingReceipt ≡ false
canonicalBruhatTitsCarrierGaugeFixingIsCarrierOnly =
  refl

canonicalBruhatTitsCarrierGaugeFixingKeepsGate3LiftObligation :
  gate3LiftObligationPreserved
    canonicalBruhatTitsCarrierGaugeFixingReceipt
  ≡ true
canonicalBruhatTitsCarrierGaugeFixingKeepsGate3LiftObligation =
  refl

canonicalBruhatTitsCarrierGaugeFixingNoYangBaxterPromotion :
  yangBaxterTheoremPromoted canonicalBruhatTitsCarrierGaugeFixingReceipt
  ≡ false
canonicalBruhatTitsCarrierGaugeFixingNoYangBaxterPromotion =
  refl

canonicalBruhatTitsCarrierGaugeFixingNoKPPromotion :
  kpTheoremPromoted canonicalBruhatTitsCarrierGaugeFixingReceipt ≡ false
canonicalBruhatTitsCarrierGaugeFixingNoKPPromotion =
  refl
