module DASHI.Physics.Closure.HolographicBulkBoundaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Holographic bulk-boundary receipt for the p-adic carrier tree.
--
-- This receipt records only the p-adic AdS/CFT dictionary needed by the
-- carrier tree analysis.  It does not promote Clay Yang-Mills or any
-- continuum Euclidean Yang-Mills construction.

data PAdicHolographyCitation : Set where
  GubserKnauteParikhSarosi2017 :
    PAdicHolographyCitation

data PAdicHolographyAuthority : Set where
  citationAuthority :
    PAdicHolographyCitation →
    PAdicHolographyAuthority

data CarrierTreeFactor : Set where
  T3 :
    CarrierTreeFactor

  T2 :
    CarrierTreeFactor

  T7 :
    CarrierTreeFactor

canonicalCarrierTreeFactors : List CarrierTreeFactor
canonicalCarrierTreeFactors = T3 ∷ T2 ∷ T7 ∷ []

data CarrierBoundaryFactor : Set where
  P1Q3 :
    CarrierBoundaryFactor

  P1Q2 :
    CarrierBoundaryFactor

  P1Q7 :
    CarrierBoundaryFactor

canonicalCarrierBoundaryFactors : List CarrierBoundaryFactor
canonicalCarrierBoundaryFactors = P1Q3 ∷ P1Q2 ∷ P1Q7 ∷ []

data HolographicDictionaryStatus : Set where
  pAdicBulkBoundaryDictionaryRecordedNoClayPromotion :
    HolographicDictionaryStatus

data WilsonLoopBoundaryMapStatus : Set where
  candidateBoundaryObservableMap :
    WilsonLoopBoundaryMapStatus

data HolographicBulkBoundaryPromotion : Set where

holographicBulkBoundaryPromotionImpossibleHere :
  HolographicBulkBoundaryPromotion →
  ⊥
holographicBulkBoundaryPromotionImpossibleHere ()

bulkBoundaryDictionaryStatement : String
bulkBoundaryDictionaryStatement =
  "p-adic AdS/CFT citation authority GubserKnauteParikhSarosi2017 records bulk Bruhat-Tits tree T_p, boundary P^1(Q_p), and bulk-to-boundary propagator given by the p-adic Poisson kernel."

productTreeBoundaryStatement : String
productTreeBoundaryStatement =
  "For the carrier product tree T_3 x T_2 x T_7, the boundary is P^1(Q_3) x P^1(Q_2) x P^1(Q_7), a product of ultrametric spaces."

wilsonLoopBoundaryStatement : String
wilsonLoopBoundaryStatement =
  "Wilson loops on the bulk Bruhat-Tits product tree map to boundary observables on the ultrametric product as a candidate holographic dictionary entry."

record HolographicBulkBoundaryReceipt : Setω where
  field
    status :
      HolographicDictionaryStatus

    pAdicAdSCFTAuthority :
      PAdicHolographyAuthority

    pAdicAdSCFTAuthorityIsGubserKnauteParikhSarosi2017 :
      pAdicAdSCFTAuthority
      ≡
      citationAuthority GubserKnauteParikhSarosi2017

    bulkGeometry :
      String

    bulkGeometryIsBruhatTitsTree :
      bulkGeometry ≡ "Bruhat-Tits tree T_p"

    boundaryGeometry :
      String

    boundaryGeometryIsProjectiveLineOverQp :
      boundaryGeometry ≡ "P^1(Q_p)"

    bulkToBoundaryPropagator :
      String

    bulkToBoundaryPropagatorIsPAdicPoissonKernel :
      bulkToBoundaryPropagator ≡ "p-adic Poisson kernel"

    carrierBulkTreeFactors :
      List CarrierTreeFactor

    carrierBulkTreeFactorsAreCanonical :
      carrierBulkTreeFactors ≡ canonicalCarrierTreeFactors

    carrierBulkProductTree :
      String

    carrierBulkProductTreeIsCanonical :
      carrierBulkProductTree ≡ "T_3 x T_2 x T_7"

    carrierBoundaryFactors :
      List CarrierBoundaryFactor

    carrierBoundaryFactorsAreCanonical :
      carrierBoundaryFactors ≡ canonicalCarrierBoundaryFactors

    carrierBoundaryProduct :
      String

    carrierBoundaryProductIsCanonical :
      carrierBoundaryProduct ≡ "P^1(Q_3) x P^1(Q_2) x P^1(Q_7)"

    boundaryIsProductOfUltrametricSpaces :
      Bool

    boundaryIsProductOfUltrametricSpacesIsTrue :
      boundaryIsProductOfUltrametricSpaces ≡ true

    holographicDictionaryForCarrierTree :
      Bool

    holographicDictionaryForCarrierTreeIsDefined :
      holographicDictionaryForCarrierTree ≡ true

    bulkToBoundaryPropagatorIsPAdicPoissonKernelCandidate :
      Bool

    bulkToBoundaryPropagatorIsPAdicPoissonKernelCandidateIsTrue :
      bulkToBoundaryPropagatorIsPAdicPoissonKernelCandidate ≡ true

    wilsonLoopOnBulkTreeMapsToBoundaryObservable :
      WilsonLoopBoundaryMapStatus

    wilsonLoopOnBulkTreeMapsToBoundaryObservableIsCandidate :
      wilsonLoopOnBulkTreeMapsToBoundaryObservable
      ≡
      candidateBoundaryObservableMap

    boundaryObservableOnUltrametricProduct :
      WilsonLoopBoundaryMapStatus

    boundaryObservableOnUltrametricProductIsCandidate :
      boundaryObservableOnUltrametricProduct
      ≡
      candidateBoundaryObservableMap

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List HolographicBulkBoundaryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    dictionaryStatement :
      String

    dictionaryStatementIsCanonical :
      dictionaryStatement ≡ bulkBoundaryDictionaryStatement

    productBoundaryStatement :
      String

    productBoundaryStatementIsCanonical :
      productBoundaryStatement ≡ productTreeBoundaryStatement

    wilsonLoopStatement :
      String

    wilsonLoopStatementIsCanonical :
      wilsonLoopStatement ≡ wilsonLoopBoundaryStatement

    receiptBoundary :
      List String

open HolographicBulkBoundaryReceipt public

canonicalHolographicBulkBoundaryReceipt :
  HolographicBulkBoundaryReceipt
canonicalHolographicBulkBoundaryReceipt =
  record
    { status =
        pAdicBulkBoundaryDictionaryRecordedNoClayPromotion
    ; pAdicAdSCFTAuthority =
        citationAuthority GubserKnauteParikhSarosi2017
    ; pAdicAdSCFTAuthorityIsGubserKnauteParikhSarosi2017 =
        refl
    ; bulkGeometry =
        "Bruhat-Tits tree T_p"
    ; bulkGeometryIsBruhatTitsTree =
        refl
    ; boundaryGeometry =
        "P^1(Q_p)"
    ; boundaryGeometryIsProjectiveLineOverQp =
        refl
    ; bulkToBoundaryPropagator =
        "p-adic Poisson kernel"
    ; bulkToBoundaryPropagatorIsPAdicPoissonKernel =
        refl
    ; carrierBulkTreeFactors =
        canonicalCarrierTreeFactors
    ; carrierBulkTreeFactorsAreCanonical =
        refl
    ; carrierBulkProductTree =
        "T_3 x T_2 x T_7"
    ; carrierBulkProductTreeIsCanonical =
        refl
    ; carrierBoundaryFactors =
        canonicalCarrierBoundaryFactors
    ; carrierBoundaryFactorsAreCanonical =
        refl
    ; carrierBoundaryProduct =
        "P^1(Q_3) x P^1(Q_2) x P^1(Q_7)"
    ; carrierBoundaryProductIsCanonical =
        refl
    ; boundaryIsProductOfUltrametricSpaces =
        true
    ; boundaryIsProductOfUltrametricSpacesIsTrue =
        refl
    ; holographicDictionaryForCarrierTree =
        true
    ; holographicDictionaryForCarrierTreeIsDefined =
        refl
    ; bulkToBoundaryPropagatorIsPAdicPoissonKernelCandidate =
        true
    ; bulkToBoundaryPropagatorIsPAdicPoissonKernelCandidateIsTrue =
        refl
    ; wilsonLoopOnBulkTreeMapsToBoundaryObservable =
        candidateBoundaryObservableMap
    ; wilsonLoopOnBulkTreeMapsToBoundaryObservableIsCandidate =
        refl
    ; boundaryObservableOnUltrametricProduct =
        candidateBoundaryObservableMap
    ; boundaryObservableOnUltrametricProductIsCandidate =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; dictionaryStatement =
        bulkBoundaryDictionaryStatement
    ; dictionaryStatementIsCanonical =
        refl
    ; productBoundaryStatement =
        productTreeBoundaryStatement
    ; productBoundaryStatementIsCanonical =
        refl
    ; wilsonLoopStatement =
        wilsonLoopBoundaryStatement
    ; wilsonLoopStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Records p-adic AdS/CFT citation authority GubserKnauteParikhSarosi2017"
        ∷ "Bulk is Bruhat-Tits tree T_p and boundary is P^1(Q_p)"
        ∷ "Bulk-to-boundary propagator is recorded as the p-adic Poisson kernel"
        ∷ "Carrier product tree boundary is P^1(Q_3) x P^1(Q_2) x P^1(Q_7)"
        ∷ "Boundary is a product of ultrametric spaces"
        ∷ "Wilson loop to boundary observable map is candidate only"
        ∷ "No Clay Yang-Mills, continuum Yang-Mills, or terminal Clay claim is promoted"
        ∷ []
    }
