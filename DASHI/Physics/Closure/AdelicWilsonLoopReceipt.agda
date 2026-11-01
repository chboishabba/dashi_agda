module DASHI.Physics.Closure.AdelicWilsonLoopReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Adelic p-adic Wilson-loop receipt.
--
-- This receipt records only the p-adic adelic spatial lattice:
-- (T_3 x T_2 x T_7) x Z_+.  Plaquettes are adjacent edge pairs in two
-- different tree directions, and the Wilson action has the usual
-- -(beta/2N) sum ReTr(U_square) form.  This is not a Euclidean continuum
-- Yang-Mills construction and does not promote any Clay claim.

data AdelicTreeDirection : Set where
  T3 :
    AdelicTreeDirection

  T2 :
    AdelicTreeDirection

  T7 :
    AdelicTreeDirection

canonicalTreeDirections : List AdelicTreeDirection
canonicalTreeDirections =
  T3 ∷ T2 ∷ T7 ∷ []

data AdelicPlaquetteType : Set where
  T3T2 :
    AdelicPlaquetteType

  T3T7 :
    AdelicPlaquetteType

  T2T7 :
    AdelicPlaquetteType

canonicalPlaquetteTypes : List AdelicPlaquetteType
canonicalPlaquetteTypes =
  T3T2 ∷ T3T7 ∷ T2T7 ∷ []

data AdelicYMCitation : Set where
  Gubser2017 :
    AdelicYMCitation

data AdelicYMAuthority : Set where
  citationAuthority :
    AdelicYMCitation →
    AdelicYMAuthority

data AdelicYMClayPromotion : Set where

adelicYMClayPromotionImpossibleHere :
  AdelicYMClayPromotion →
  ⊥
adelicYMClayPromotionImpossibleHere ()

pAdicSpatialLatticeLabel : String
pAdicSpatialLatticeLabel =
  "T_3 x T_2 x T_7"

fullPAdicFourDimensionalLatticeLabel : String
fullPAdicFourDimensionalLatticeLabel =
  "(T_3 x T_2 x T_7) x Z_+"

wilsonActionFormula : String
wilsonActionFormula =
  "S = -(beta/2N) sum_square ReTr(U_square)"

plaquetteConstructionStatement : String
plaquetteConstructionStatement =
  "Plaquettes are adjacent edge pairs in different Bruhat-Tits tree directions."

record AdelicWilsonLoopReceipt : Setω where
  field
    pAdicSpatialLattice :
      String

    pAdicSpatialLatticeIsProductTree :
      pAdicSpatialLattice ≡ pAdicSpatialLatticeLabel

    treeDirections :
      List AdelicTreeDirection

    treeDirectionsAreCanonical :
      treeDirections ≡ canonicalTreeDirections

    plaquetteTypes :
      List AdelicPlaquetteType

    plaquetteTypesAreCanonical :
      plaquetteTypes ≡ canonicalPlaquetteTypes

    plaquettesFromAdjacentEdgePairs :
      Bool

    plaquettesFromAdjacentEdgePairsIsTrue :
      plaquettesFromAdjacentEdgePairs ≡ true

    plaquettesUseDifferentTreeDirections :
      Bool

    plaquettesUseDifferentTreeDirectionsIsTrue :
      plaquettesUseDifferentTreeDirections ≡ true

    t3t2PlaquetteCountPerVertex :
      Nat

    t3t2PlaquetteCountPerVertexIsTwelve :
      t3t2PlaquetteCountPerVertex ≡ 12

    t3t7PlaquetteCountPerVertex :
      Nat

    t3t7PlaquetteCountPerVertexIsThirtyTwo :
      t3t7PlaquetteCountPerVertex ≡ 32

    t2t7PlaquetteCountPerVertex :
      Nat

    t2t7PlaquetteCountPerVertexIsTwentyFour :
      t2t7PlaquetteCountPerVertex ≡ 24

    plaquetteCountPerVertex :
      Nat

    plaquetteCountPerVertexIsSixtyEight :
      plaquetteCountPerVertex ≡ 68

    wilsonAction :
      String

    wilsonActionIsCanonical :
      wilsonAction ≡ wilsonActionFormula

    reflectionPositivityOnTree :
      AdelicYMAuthority

    reflectionPositivityOnTreeIsGubser2017 :
      reflectionPositivityOnTree ≡ citationAuthority Gubser2017

    euclideanTimeDirection :
      String

    euclideanTimeDirectionIsDepth :
      euclideanTimeDirection ≡ "Z_+ depth"

    fullLattice :
      String

    fullLatticeIsProductTreeTimesDepth :
      fullLattice ≡ fullPAdicFourDimensionalLatticeLabel

    ymPAdicLatticeFullyDefined :
      Bool

    ymPAdicLatticeFullyDefinedIsTrue :
      ymPAdicLatticeFullyDefined ≡ true

    pAdicComponentOnly :
      Bool

    pAdicComponentOnlyIsTrue :
      pAdicComponentOnly ≡ true

    continuumEuclideanYMConstructed :
      Bool

    continuumEuclideanYMConstructedIsFalse :
      continuumEuclideanYMConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List AdelicYMClayPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    plaquetteConstruction :
      String

    plaquetteConstructionIsCanonical :
      plaquetteConstruction ≡ plaquetteConstructionStatement

    receiptBoundary :
      List String

open AdelicWilsonLoopReceipt public

canonicalAdelicWilsonLoopReceipt :
  AdelicWilsonLoopReceipt
canonicalAdelicWilsonLoopReceipt =
  record
    { pAdicSpatialLattice =
        pAdicSpatialLatticeLabel
    ; pAdicSpatialLatticeIsProductTree =
        refl
    ; treeDirections =
        canonicalTreeDirections
    ; treeDirectionsAreCanonical =
        refl
    ; plaquetteTypes =
        canonicalPlaquetteTypes
    ; plaquetteTypesAreCanonical =
        refl
    ; plaquettesFromAdjacentEdgePairs =
        true
    ; plaquettesFromAdjacentEdgePairsIsTrue =
        refl
    ; plaquettesUseDifferentTreeDirections =
        true
    ; plaquettesUseDifferentTreeDirectionsIsTrue =
        refl
    ; t3t2PlaquetteCountPerVertex =
        12
    ; t3t2PlaquetteCountPerVertexIsTwelve =
        refl
    ; t3t7PlaquetteCountPerVertex =
        32
    ; t3t7PlaquetteCountPerVertexIsThirtyTwo =
        refl
    ; t2t7PlaquetteCountPerVertex =
        24
    ; t2t7PlaquetteCountPerVertexIsTwentyFour =
        refl
    ; plaquetteCountPerVertex =
        68
    ; plaquetteCountPerVertexIsSixtyEight =
        refl
    ; wilsonAction =
        wilsonActionFormula
    ; wilsonActionIsCanonical =
        refl
    ; reflectionPositivityOnTree =
        citationAuthority Gubser2017
    ; reflectionPositivityOnTreeIsGubser2017 =
        refl
    ; euclideanTimeDirection =
        "Z_+ depth"
    ; euclideanTimeDirectionIsDepth =
        refl
    ; fullLattice =
        fullPAdicFourDimensionalLatticeLabel
    ; fullLatticeIsProductTreeTimesDepth =
        refl
    ; ymPAdicLatticeFullyDefined =
        true
    ; ymPAdicLatticeFullyDefinedIsTrue =
        refl
    ; pAdicComponentOnly =
        true
    ; pAdicComponentOnlyIsTrue =
        refl
    ; continuumEuclideanYMConstructed =
        false
    ; continuumEuclideanYMConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; plaquetteConstruction =
        plaquetteConstructionStatement
    ; plaquetteConstructionIsCanonical =
        refl
    ; receiptBoundary =
        "The p-adic spatial lattice is the Bruhat-Tits product T_3 x T_2 x T_7"
        ∷ "Plaquettes are adjacent edge pairs in distinct tree directions"
        ∷ "Plaquette counts per vertex are T3-T2 = 12, T3-T7 = 32, T2-T7 = 24, total = 68"
        ∷ "The Wilson action is S = -(beta/2N) sum_square ReTr(U_square)"
        ∷ "Reflection positivity on the tree is inherited with citationAuthority Gubser2017"
        ∷ "The full p-adic four-dimensional lattice is (T_3 x T_2 x T_7) x Z_+"
        ∷ "This receipt defines the p-adic lattice only and does not promote Euclidean continuum Yang-Mills or Clay Yang-Mills"
        ∷ []
    }

ymPAdicLatticeFullyDefinedFlag :
  ymPAdicLatticeFullyDefined canonicalAdelicWilsonLoopReceipt ≡ true
ymPAdicLatticeFullyDefinedFlag =
  ymPAdicLatticeFullyDefinedIsTrue canonicalAdelicWilsonLoopReceipt

plaquetteCountPerVertexFlag :
  plaquetteCountPerVertex canonicalAdelicWilsonLoopReceipt ≡ 68
plaquetteCountPerVertexFlag =
  plaquetteCountPerVertexIsSixtyEight canonicalAdelicWilsonLoopReceipt

noEuclideanContinuumPromotionFlag :
  continuumEuclideanYMConstructed canonicalAdelicWilsonLoopReceipt ≡ false
noEuclideanContinuumPromotionFlag =
  continuumEuclideanYMConstructedIsFalse canonicalAdelicWilsonLoopReceipt

noClayYangMillsPromotionFlag :
  clayYangMillsPromoted canonicalAdelicWilsonLoopReceipt ≡ false
noClayYangMillsPromotionFlag =
  clayYangMillsPromotedIsFalse canonicalAdelicWilsonLoopReceipt
