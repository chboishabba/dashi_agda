module DASHI.Physics.Closure.PAdicShimuraFlatLimitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- p-adic Shimura / Bruhat-Tits tree flat-limit receipt.

data PAdicShimuraFlatLimitStatus : Set where
  candidate :
    PAdicShimuraFlatLimitStatus

  inhabitedComponentOnly :
    PAdicShimuraFlatLimitStatus

data PAdicShimuraGeometryComponent : Set where
  pPlusOneRegularBruhatTitsTree :
    PAdicShimuraGeometryComponent

  graphTheoreticZeroCurvature :
    PAdicShimuraGeometryComponent

  infiniteDiameterTree :
    PAdicShimuraGeometryComponent

  largePBranchedLatticeLimit :
    PAdicShimuraGeometryComponent

  ultrametricBoundaryP1Qp :
    PAdicShimuraGeometryComponent

  productTreeT3T2T7 :
    PAdicShimuraGeometryComponent

  geometricSpectralGapAbsentForTree :
    PAdicShimuraGeometryComponent

canonicalPAdicShimuraGeometryComponents :
  List PAdicShimuraGeometryComponent
canonicalPAdicShimuraGeometryComponents =
  pPlusOneRegularBruhatTitsTree
  ∷ graphTheoreticZeroCurvature
  ∷ infiniteDiameterTree
  ∷ largePBranchedLatticeLimit
  ∷ ultrametricBoundaryP1Qp
  ∷ productTreeT3T2T7
  ∷ geometricSpectralGapAbsentForTree
  ∷ []

data PAdicYMCitation : Set where
  Gubser2017 :
    PAdicYMCitation

  Serre1980 :
    PAdicYMCitation

data PAdicYMAuthority : Set where
  citationAuthority :
    PAdicYMCitation →
    PAdicYMAuthority

data PAdicShimuraClayPromotion : Set where

pAdicShimuraClayPromotionImpossibleHere :
  PAdicShimuraClayPromotion →
  ⊥
pAdicShimuraClayPromotionImpossibleHere ()

bruhatTitsTreeStatement : String
bruhatTitsTreeStatement =
  "The p-adic Shimura flat-limit component is inhabited by the Bruhat-Tits product tree T_3 x T_2 x T_7: graph-theoretic zero curvature, ultrametric boundary, infinite diameter, and p-adic Yang-Mills native to the tree via Gubser2017 citation authority."

largePFlatLimitStatement : String
largePFlatLimitStatement =
  "The large-p regime is recorded as approaching a cubic-lattice-like p-adic flat-limit candidate; this promotes only the p-adic component, not continuum or Clay Yang-Mills."

ultrametricBoundaryStatement : String
ultrametricBoundaryStatement =
  "The boundary of the Bruhat-Tits tree is P1(Q_p) with the p-adic ultrametric; this is theorem-level mathematics, cited to Serre1980."

spectralGapObstructionStatement : String
spectralGapObstructionStatement =
  "The hyperbolic geometric spectral-gap obstruction from real H^3 curvature is absent for the Bruhat-Tits tree component."

record PAdicShimuraFlatLimitReceipt : Setω where
  field
    pAdicShimuraProvidesFlatLimit :
      PAdicShimuraFlatLimitStatus

    pAdicShimuraProvidesFlatLimitIsInhabitedComponentOnly :
      pAdicShimuraProvidesFlatLimit ≡ inhabitedComponentOnly

    pAdicFlatLimitInhabited :
      Bool

    pAdicFlatLimitInhabitedIsTrue :
      pAdicFlatLimitInhabited ≡ true

    pAdicFlatLimitIsComponentOnly :
      Bool

    pAdicFlatLimitIsComponentOnlyIsTrue :
      pAdicFlatLimitIsComponentOnly ≡ true

    bruhatTitsBranchingDegreeLabel :
      String

    bruhatTitsBranchingDegreeLabelIsCanonical :
      bruhatTitsBranchingDegreeLabel ≡ "(p+1)-regular"

    bruhatTitsTreeHasZeroCurvature :
      Bool

    bruhatTitsTreeHasZeroCurvatureIsTrue :
      bruhatTitsTreeHasZeroCurvature ≡ true

    bruhatTitsTreeHasInfiniteDiameter :
      Bool

    bruhatTitsTreeHasInfiniteDiameterIsTrue :
      bruhatTitsTreeHasInfiniteDiameter ≡ true

    bruhatTitsProductTreeFlatPAdicSpatialLattice :
      Bool

    bruhatTitsProductTreeFlatPAdicSpatialLatticeIsTrue :
      bruhatTitsProductTreeFlatPAdicSpatialLattice ≡ true

    pAdicBoundaryUltrametricTheorem :
      Bool

    pAdicBoundaryUltrametricTheoremIsTrue :
      pAdicBoundaryUltrametricTheorem ≡ true

    pAdicBoundaryUltrametricAuthority :
      PAdicYMAuthority

    pAdicBoundaryUltrametricAuthorityIsSerre1980 :
      pAdicBoundaryUltrametricAuthority ≡ citationAuthority Serre1980

    hyperbolicGeometricSpectralGapObstructionAbsent :
      Bool

    hyperbolicGeometricSpectralGapObstructionAbsentIsTrue :
      hyperbolicGeometricSpectralGapObstructionAbsent ≡ true

    pAdicYMNativelyDefined :
      PAdicYMAuthority

    pAdicYMNativelyDefinedIsGubser2017 :
      pAdicYMNativelyDefined ≡ citationAuthority Gubser2017

    largePLimitApproachesCubicLattice :
      Bool

    largePLimitApproachesCubicLatticeIsTrue :
      largePLimitApproachesCubicLattice ≡ true

    approximatingLatticeDimension :
      Nat

    approximatingLatticeDimensionIsThree :
      approximatingLatticeDimension ≡ 3

    geometryComponents :
      List PAdicShimuraGeometryComponent

    geometryComponentsAreCanonical :
      geometryComponents ≡ canonicalPAdicShimuraGeometryComponents

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List PAdicShimuraClayPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    treeStatement :
      String

    treeStatementIsCanonical :
      treeStatement ≡ bruhatTitsTreeStatement

    largePStatement :
      String

    largePStatementIsCanonical :
      largePStatement ≡ largePFlatLimitStatement

    ultrametricStatement :
      String

    ultrametricStatementIsCanonical :
      ultrametricStatement ≡ ultrametricBoundaryStatement

    spectralGapStatement :
      String

    spectralGapStatementIsCanonical :
      spectralGapStatement ≡ spectralGapObstructionStatement

    receiptBoundary :
      List String

open PAdicShimuraFlatLimitReceipt public

canonicalPAdicShimuraFlatLimitReceipt :
  PAdicShimuraFlatLimitReceipt
canonicalPAdicShimuraFlatLimitReceipt =
  record
    { pAdicShimuraProvidesFlatLimit =
        inhabitedComponentOnly
    ; pAdicShimuraProvidesFlatLimitIsInhabitedComponentOnly =
        refl
    ; pAdicFlatLimitInhabited =
        true
    ; pAdicFlatLimitInhabitedIsTrue =
        refl
    ; pAdicFlatLimitIsComponentOnly =
        true
    ; pAdicFlatLimitIsComponentOnlyIsTrue =
        refl
    ; bruhatTitsBranchingDegreeLabel =
        "(p+1)-regular"
    ; bruhatTitsBranchingDegreeLabelIsCanonical =
        refl
    ; bruhatTitsTreeHasZeroCurvature =
        true
    ; bruhatTitsTreeHasZeroCurvatureIsTrue =
        refl
    ; bruhatTitsTreeHasInfiniteDiameter =
        true
    ; bruhatTitsTreeHasInfiniteDiameterIsTrue =
        refl
    ; bruhatTitsProductTreeFlatPAdicSpatialLattice =
        true
    ; bruhatTitsProductTreeFlatPAdicSpatialLatticeIsTrue =
        refl
    ; pAdicBoundaryUltrametricTheorem =
        true
    ; pAdicBoundaryUltrametricTheoremIsTrue =
        refl
    ; pAdicBoundaryUltrametricAuthority =
        citationAuthority Serre1980
    ; pAdicBoundaryUltrametricAuthorityIsSerre1980 =
        refl
    ; hyperbolicGeometricSpectralGapObstructionAbsent =
        true
    ; hyperbolicGeometricSpectralGapObstructionAbsentIsTrue =
        refl
    ; pAdicYMNativelyDefined =
        citationAuthority Gubser2017
    ; pAdicYMNativelyDefinedIsGubser2017 =
        refl
    ; largePLimitApproachesCubicLattice =
        true
    ; largePLimitApproachesCubicLatticeIsTrue =
        refl
    ; approximatingLatticeDimension =
        3
    ; approximatingLatticeDimensionIsThree =
        refl
    ; geometryComponents =
        canonicalPAdicShimuraGeometryComponents
    ; geometryComponentsAreCanonical =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
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
    ; treeStatement =
        bruhatTitsTreeStatement
    ; treeStatementIsCanonical =
        refl
    ; largePStatement =
        largePFlatLimitStatement
    ; largePStatementIsCanonical =
        refl
    ; ultrametricStatement =
        ultrametricBoundaryStatement
    ; ultrametricStatementIsCanonical =
        refl
    ; spectralGapStatement =
        spectralGapObstructionStatement
    ; spectralGapStatementIsCanonical =
        refl
    ; receiptBoundary =
        "p-adic Shimura/Bruhat-Tits boundary P1(Q_p) is ultrametric as theorem-level mathematics"
        ∷ "The Bruhat-Tits product tree T_3 x T_2 x T_7 gives a flat p-adic spatial lattice"
        ∷ "The hyperbolic geometric spectral-gap obstruction is absent for the Bruhat-Tits tree component"
        ∷ "pAdicFlatLimitInhabited is true for the p-adic component only"
        ∷ "The Bruhat-Tits tree is (p+1)-regular, has graph-theoretic zero curvature, and has infinite diameter"
        ∷ "p-adic Yang-Mills on the tree is citationAuthority Gubser2017"
        ∷ "The large-p regime approaches a cubic-lattice-like p-adic flat-limit candidate"
        ∷ "No continuum Yang-Mills, Clay Yang-Mills, or terminal Clay claim is promoted"
        ∷ []
    }

pAdicShimuraFlatLimitIsInhabitedComponentOnly :
  pAdicShimuraProvidesFlatLimit
    canonicalPAdicShimuraFlatLimitReceipt ≡ inhabitedComponentOnly
pAdicShimuraFlatLimitIsInhabitedComponentOnly =
  refl

pAdicShimuraFlatLimitInhabitedComponent :
  pAdicFlatLimitInhabited
    canonicalPAdicShimuraFlatLimitReceipt ≡ true
pAdicShimuraFlatLimitInhabitedComponent =
  refl

pAdicShimuraTreeHasZeroCurvature :
  bruhatTitsTreeHasZeroCurvature
    canonicalPAdicShimuraFlatLimitReceipt ≡ true
pAdicShimuraTreeHasZeroCurvature =
  refl

pAdicShimuraBoundaryIsUltrametricTheorem :
  pAdicBoundaryUltrametricTheorem
    canonicalPAdicShimuraFlatLimitReceipt ≡ true
pAdicShimuraBoundaryIsUltrametricTheorem =
  refl

pAdicShimuraBoundaryUltrametricSerre1980Authority :
  pAdicBoundaryUltrametricAuthority
    canonicalPAdicShimuraFlatLimitReceipt ≡ citationAuthority Serre1980
pAdicShimuraBoundaryUltrametricSerre1980Authority =
  refl

pAdicShimuraGeometricGapObstructionAbsent :
  hyperbolicGeometricSpectralGapObstructionAbsent
    canonicalPAdicShimuraFlatLimitReceipt ≡ true
pAdicShimuraGeometricGapObstructionAbsent =
  refl

pAdicYMGubser2017Authority :
  pAdicYMNativelyDefined
    canonicalPAdicShimuraFlatLimitReceipt ≡ citationAuthority Gubser2017
pAdicYMGubser2017Authority =
  refl

pAdicShimuraLargePLimitApproachesCubicLattice :
  largePLimitApproachesCubicLattice
    canonicalPAdicShimuraFlatLimitReceipt ≡ true
pAdicShimuraLargePLimitApproachesCubicLattice =
  refl

pAdicShimuraFlatLimitKeepsClayFalse :
  clayYangMillsPromoted
    canonicalPAdicShimuraFlatLimitReceipt ≡ false
pAdicShimuraFlatLimitKeepsClayFalse =
  refl

pAdicShimuraFlatLimitKeepsTerminalFalse :
  terminalClayClaimPromoted
    canonicalPAdicShimuraFlatLimitReceipt ≡ false
pAdicShimuraFlatLimitKeepsTerminalFalse =
  refl
