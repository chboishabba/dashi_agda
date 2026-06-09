module DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS A2 triadic shell Bernstein/Hölder boundary.
--
-- This module records the fail-closed analytic target for the A2
-- Navier-Stokes triadic shell proof lane:
--
--   ||P_j u · ∇P_k ω||_L2
--     <= C * 2^min(j,k) * ||P_j u||_L2 * ||P_k ω||_L2
--
-- The estimate is the desired/tight dyadic target.  The naive Bernstein
-- L4 route is recorded here, but deliberately not promoted: applying
-- Hölder L4 x L4 and then Bernstein shell-by-shell loses the needed
-- near-diagonal structure and does not certify the tight 2^min(j,k)
-- factor uniformly at the A2 boundary.  The remaining proof obligation is
-- a near-diagonal Coifman-Meyer bilinear multiplier estimate adapted to
-- the true Leray triadic shell geometry.
--
-- Boundary status:
--
--   boundary recorded                 true
--   estimate target recorded          true
--   naive route recorded              true
--   tight estimate proved             false
--   clayNavierStokesPromoted          false
--
-- This is a boundary receipt only.  It records the target, the rejected
-- shortcut, the required near-diagonal route, blockers, exact row counts,
-- and canonical refl proofs.  It does not prove the tight shell estimate,
-- does not discharge the Coifman-Meyer symbol analysis, and does not
-- promote Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Shell and dyadic carriers.

data DyadicIndex : Set where
  velocityIndex-j :
    DyadicIndex
  vorticityIndex-k :
    DyadicIndex
  minimumIndex-minjk :
    DyadicIndex
  nearDiagonalIndex :
    DyadicIndex
  separatedOffDiagonalIndex :
    DyadicIndex

data LPShell : Set where
  velocityLittlewoodPaleyShell-Pj-u :
    DyadicIndex →
    LPShell
  vorticityLittlewoodPaleyShell-Pk-omega :
    DyadicIndex →
    LPShell
  gradientVorticityShell-grad-Pk-omega :
    DyadicIndex →
    LPShell
  productOutputShell :
    DyadicIndex →
    DyadicIndex →
    LPShell
  nearDiagonalTriadicShell :
    DyadicIndex →
    DyadicIndex →
    LPShell

canonicalVelocityIndex : DyadicIndex
canonicalVelocityIndex =
  velocityIndex-j

canonicalVorticityIndex : DyadicIndex
canonicalVorticityIndex =
  vorticityIndex-k

canonicalMinimumIndex : DyadicIndex
canonicalMinimumIndex =
  minimumIndex-minjk

canonicalNearDiagonalIndex : DyadicIndex
canonicalNearDiagonalIndex =
  nearDiagonalIndex

canonicalVelocityShell : LPShell
canonicalVelocityShell =
  velocityLittlewoodPaleyShell-Pj-u canonicalVelocityIndex

canonicalVorticityShell : LPShell
canonicalVorticityShell =
  vorticityLittlewoodPaleyShell-Pk-omega canonicalVorticityIndex

canonicalGradientVorticityShell : LPShell
canonicalGradientVorticityShell =
  gradientVorticityShell-grad-Pk-omega canonicalVorticityIndex

canonicalProductOutputShell : LPShell
canonicalProductOutputShell =
  productOutputShell canonicalVelocityIndex canonicalVorticityIndex

canonicalNearDiagonalShell : LPShell
canonicalNearDiagonalShell =
  nearDiagonalTriadicShell
    canonicalVelocityIndex
    canonicalVorticityIndex

canonicalLPShells : List LPShell
canonicalLPShells =
  canonicalVelocityShell
  ∷ canonicalVorticityShell
  ∷ canonicalGradientVorticityShell
  ∷ canonicalProductOutputShell
  ∷ canonicalNearDiagonalShell
  ∷ []

lpShellCount : Nat
lpShellCount =
  listLength canonicalLPShells

lpShellCountIs5 :
  lpShellCount ≡ 5
lpShellCountIs5 =
  refl

canonicalDyadicIndices : List DyadicIndex
canonicalDyadicIndices =
  canonicalVelocityIndex
  ∷ canonicalVorticityIndex
  ∷ canonicalMinimumIndex
  ∷ canonicalNearDiagonalIndex
  ∷ separatedOffDiagonalIndex
  ∷ []

dyadicIndexCount : Nat
dyadicIndexCount =
  listLength canonicalDyadicIndices

dyadicIndexCountIs5 :
  dyadicIndexCount ≡ 5
dyadicIndexCountIs5 =
  refl

------------------------------------------------------------------------
-- Desired/tight estimate target.

desiredTightTargetEstimateText : String
desiredTightTargetEstimateText =
  "||P_j u · ∇P_k ω||_L2 <= C * 2^min(j,k) * ||P_j u||_L2 * ||P_k ω||_L2"

data TriadicShellNormFactor : Set where
  leftHandSide-L2-Pj-u-dot-grad-Pk-omega :
    LPShell →
    LPShell →
    TriadicShellNormFactor
  constant-C :
    TriadicShellNormFactor
  dyadicGain-2-to-min-j-k :
    DyadicIndex →
    TriadicShellNormFactor
  velocityShell-L2-norm :
    LPShell →
    TriadicShellNormFactor
  vorticityShell-L2-norm :
    LPShell →
    TriadicShellNormFactor

canonicalEstimateFactors : List TriadicShellNormFactor
canonicalEstimateFactors =
  leftHandSide-L2-Pj-u-dot-grad-Pk-omega
    canonicalVelocityShell
    canonicalGradientVorticityShell
  ∷ constant-C
  ∷ dyadicGain-2-to-min-j-k canonicalMinimumIndex
  ∷ velocityShell-L2-norm canonicalVelocityShell
  ∷ vorticityShell-L2-norm canonicalVorticityShell
  ∷ []

estimateFactorCount : Nat
estimateFactorCount =
  listLength canonicalEstimateFactors

estimateFactorCountIs5 :
  estimateFactorCount ≡ 5
estimateFactorCountIs5 =
  refl

data TightTriadicShellEstimateTarget : Set where
  desiredTightBernsteinHolderA2Target :
    String →
    List TriadicShellNormFactor →
    TightTriadicShellEstimateTarget

canonicalTightTriadicShellEstimateTarget :
  TightTriadicShellEstimateTarget
canonicalTightTriadicShellEstimateTarget =
  desiredTightBernsteinHolderA2Target
    desiredTightTargetEstimateText
    canonicalEstimateFactors

------------------------------------------------------------------------
-- Naive Bernstein/Hölder route and insufficiency.

data BernsteinRoute : Set where
  naiveHolder-L4xL4-then-Bernstein :
    LPShell →
    LPShell →
    BernsteinRoute
  velocityShellL2-to-L4-Bernstein :
    DyadicIndex →
    BernsteinRoute
  gradientVorticityShellL2-to-L4-Bernstein :
    DyadicIndex →
    BernsteinRoute
  naiveRouteRecordsOnlyDimensionalControl :
    BernsteinRoute

canonicalNaiveBernsteinRoutes : List BernsteinRoute
canonicalNaiveBernsteinRoutes =
  naiveHolder-L4xL4-then-Bernstein
    canonicalVelocityShell
    canonicalGradientVorticityShell
  ∷ velocityShellL2-to-L4-Bernstein canonicalVelocityIndex
  ∷ gradientVorticityShellL2-to-L4-Bernstein canonicalVorticityIndex
  ∷ naiveRouteRecordsOnlyDimensionalControl
  ∷ []

naiveBernsteinRouteCount : Nat
naiveBernsteinRouteCount =
  listLength canonicalNaiveBernsteinRoutes

naiveBernsteinRouteCountIs4 :
  naiveBernsteinRouteCount ≡ 4
naiveBernsteinRouteCountIs4 =
  refl

data NaiveRouteInsufficiency : Set where
  L4xL4RouteDoesNotExposeTriadicSymbolCancellation :
    NaiveRouteInsufficiency
  shellwiseBernsteinLosesNearDiagonalSharpness :
    NaiveRouteInsufficiency
  gradientPlacedOnPkOmegaCanOverpayByMaxShell :
    NaiveRouteInsufficiency
  targetRequiresTwoToMinjkNotNaiveSeparatedShellLoss :
    NaiveRouteInsufficiency
  noClayPromotionFromNaiveHolderBernsteinBound :
    NaiveRouteInsufficiency

canonicalNaiveRouteInsufficiencies :
  List NaiveRouteInsufficiency
canonicalNaiveRouteInsufficiencies =
  L4xL4RouteDoesNotExposeTriadicSymbolCancellation
  ∷ shellwiseBernsteinLosesNearDiagonalSharpness
  ∷ gradientPlacedOnPkOmegaCanOverpayByMaxShell
  ∷ targetRequiresTwoToMinjkNotNaiveSeparatedShellLoss
  ∷ noClayPromotionFromNaiveHolderBernsteinBound
  ∷ []

naiveRouteInsufficiencyCount : Nat
naiveRouteInsufficiencyCount =
  listLength canonicalNaiveRouteInsufficiencies

naiveRouteInsufficiencyCountIs5 :
  naiveRouteInsufficiencyCount ≡ 5
naiveRouteInsufficiencyCountIs5 =
  refl

------------------------------------------------------------------------
-- Required near-diagonal Coifman-Meyer route.

data CoifmanMeyerNearDiagonalRoute : Set where
  localizeToNearDiagonalTriadicShells :
    LPShell →
    CoifmanMeyerNearDiagonalRoute
  proveUniformBilinearSymbolDerivativeBounds :
    DyadicIndex →
    DyadicIndex →
    CoifmanMeyerNearDiagonalRoute
  exploitLerayProjectionTriadicGeometry :
    CoifmanMeyerNearDiagonalRoute
  recoverSharpTwoToMinjkDerivativePlacement :
    DyadicIndex →
    CoifmanMeyerNearDiagonalRoute
  closeL2xL2ToL2BilinearMultiplierEstimate :
    TightTriadicShellEstimateTarget →
    CoifmanMeyerNearDiagonalRoute

canonicalCoifmanMeyerNearDiagonalRoutes :
  List CoifmanMeyerNearDiagonalRoute
canonicalCoifmanMeyerNearDiagonalRoutes =
  localizeToNearDiagonalTriadicShells canonicalNearDiagonalShell
  ∷ proveUniformBilinearSymbolDerivativeBounds
      canonicalVelocityIndex
      canonicalVorticityIndex
  ∷ exploitLerayProjectionTriadicGeometry
  ∷ recoverSharpTwoToMinjkDerivativePlacement canonicalMinimumIndex
  ∷ closeL2xL2ToL2BilinearMultiplierEstimate
      canonicalTightTriadicShellEstimateTarget
  ∷ []

coifmanMeyerNearDiagonalRouteCount : Nat
coifmanMeyerNearDiagonalRouteCount =
  listLength canonicalCoifmanMeyerNearDiagonalRoutes

coifmanMeyerNearDiagonalRouteCountIs5 :
  coifmanMeyerNearDiagonalRouteCount ≡ 5
coifmanMeyerNearDiagonalRouteCountIs5 =
  refl

------------------------------------------------------------------------
-- Blockers and fail-closed flags.

data NSTriadicShellBernsteinHolderBlocker : Set where
  naiveBernsteinL4RouteInsufficient :
    NSTriadicShellBernsteinHolderBlocker
  missingNearDiagonalCoifmanMeyerSymbolBounds :
    NSTriadicShellBernsteinHolderBlocker
  missingSharpDerivativePlacementAtTwoToMinjk :
    NSTriadicShellBernsteinHolderBlocker
  missingLerayTriadicCancellationLedger :
    NSTriadicShellBernsteinHolderBlocker
  missingOffDiagonalSummabilitySeparation :
    NSTriadicShellBernsteinHolderBlocker
  missingA2ShellToCriticalResidualTransfer :
    NSTriadicShellBernsteinHolderBlocker
  clayNavierStokesPromotionClosed :
    NSTriadicShellBernsteinHolderBlocker

canonicalNSTriadicShellBernsteinHolderBlockers :
  List NSTriadicShellBernsteinHolderBlocker
canonicalNSTriadicShellBernsteinHolderBlockers =
  naiveBernsteinL4RouteInsufficient
  ∷ missingNearDiagonalCoifmanMeyerSymbolBounds
  ∷ missingSharpDerivativePlacementAtTwoToMinjk
  ∷ missingLerayTriadicCancellationLedger
  ∷ missingOffDiagonalSummabilitySeparation
  ∷ missingA2ShellToCriticalResidualTransfer
  ∷ clayNavierStokesPromotionClosed
  ∷ []

blockerCount : Nat
blockerCount =
  listLength canonicalNSTriadicShellBernsteinHolderBlockers

blockerCountIs7 :
  blockerCount ≡ 7
blockerCountIs7 =
  refl

boundaryRecorded : Bool
boundaryRecorded =
  true

estimateTargetRecorded : Bool
estimateTargetRecorded =
  true

naiveRouteRecorded : Bool
naiveRouteRecorded =
  true

tightEstimateProved : Bool
tightEstimateProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

boundaryRecordedIsTrue :
  boundaryRecorded ≡ true
boundaryRecordedIsTrue =
  refl

estimateTargetRecordedIsTrue :
  estimateTargetRecorded ≡ true
estimateTargetRecordedIsTrue =
  refl

naiveRouteRecordedIsTrue :
  naiveRouteRecorded ≡ true
naiveRouteRecordedIsTrue =
  refl

tightEstimateProvedIsFalse :
  tightEstimateProved ≡ false
tightEstimateProvedIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

------------------------------------------------------------------------
-- Compact O/R/C/S/L/P/G/F ledger rows.

data ORCSLPGFRow : Set where
  O-boundaryObjectRecorded :
    ORCSLPGFRow
  R-tightEstimateRequirementRecorded :
    ORCSLPGFRow
  C-carriersShellIndexRouteBlockerAndFlagTyped :
    ORCSLPGFRow
  S-stateFailClosedNoPromotion :
    ORCSLPGFRow
  L-latticeNaiveRouteBelowCoifmanMeyerRoute :
    ORCSLPGFRow
  P-proposalProveNearDiagonalCoifmanMeyer :
    ORCSLPGFRow
  G-governanceClayPromotionClosed :
    ORCSLPGFRow
  F-gapTightEstimateStillFalse :
    ORCSLPGFRow

canonicalORCSLPGFRows : List ORCSLPGFRow
canonicalORCSLPGFRows =
  O-boundaryObjectRecorded
  ∷ R-tightEstimateRequirementRecorded
  ∷ C-carriersShellIndexRouteBlockerAndFlagTyped
  ∷ S-stateFailClosedNoPromotion
  ∷ L-latticeNaiveRouteBelowCoifmanMeyerRoute
  ∷ P-proposalProveNearDiagonalCoifmanMeyer
  ∷ G-governanceClayPromotionClosed
  ∷ F-gapTightEstimateStillFalse
  ∷ []

orcsLpgfRowCount : Nat
orcsLpgfRowCount =
  listLength canonicalORCSLPGFRows

orcsLpgfRowCountIs8 :
  orcsLpgfRowCount ≡ 8
orcsLpgfRowCountIs8 =
  refl

canonicalORCSLPGFSummary : String
canonicalORCSLPGFSummary =
  "O boundary receipt; R tight 2^min(j,k) L2 target; C LP shells, indices, routes, blockers, booleans; S fail-closed; L naive L4 route below near-diagonal Coifman-Meyer; P prove Coifman-Meyer shell estimate; G no Clay promotion; F tight estimate unproved."

------------------------------------------------------------------------
-- Canonical receipt.

record NSTriadicShellBernsteinHolderBoundary : Set where
  constructor nsTriadicShellBernsteinHolderBoundary
  field
    moduleName :
      String
    moduleNameIsCanonical :
      moduleName
        ≡ "DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary"
    dyadicIndices :
      List DyadicIndex
    dyadicIndicesAreCanonical :
      dyadicIndices ≡ canonicalDyadicIndices
    dyadicIndexCountField :
      dyadicIndexCount ≡ 5
    lpShells :
      List LPShell
    lpShellsAreCanonical :
      lpShells ≡ canonicalLPShells
    lpShellCountField :
      lpShellCount ≡ 5
    tightEstimateTarget :
      TightTriadicShellEstimateTarget
    tightEstimateTargetIsCanonical :
      tightEstimateTarget
        ≡ canonicalTightTriadicShellEstimateTarget
    estimateFactors :
      List TriadicShellNormFactor
    estimateFactorsAreCanonical :
      estimateFactors ≡ canonicalEstimateFactors
    estimateFactorCountField :
      estimateFactorCount ≡ 5
    naiveBernsteinRoutes :
      List BernsteinRoute
    naiveBernsteinRoutesAreCanonical :
      naiveBernsteinRoutes ≡ canonicalNaiveBernsteinRoutes
    naiveBernsteinRouteCountField :
      naiveBernsteinRouteCount ≡ 4
    naiveInsufficiencies :
      List NaiveRouteInsufficiency
    naiveInsufficienciesAreCanonical :
      naiveInsufficiencies ≡ canonicalNaiveRouteInsufficiencies
    naiveRouteInsufficiencyCountField :
      naiveRouteInsufficiencyCount ≡ 5
    coifmanMeyerNearDiagonalRoutes :
      List CoifmanMeyerNearDiagonalRoute
    coifmanMeyerNearDiagonalRoutesAreCanonical :
      coifmanMeyerNearDiagonalRoutes
        ≡ canonicalCoifmanMeyerNearDiagonalRoutes
    coifmanMeyerNearDiagonalRouteCountField :
      coifmanMeyerNearDiagonalRouteCount ≡ 5
    blockers :
      List NSTriadicShellBernsteinHolderBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSTriadicShellBernsteinHolderBlockers
    blockerCountField :
      blockerCount ≡ 7
    orcsLpgfRows :
      List ORCSLPGFRow
    orcsLpgfRowsAreCanonical :
      orcsLpgfRows ≡ canonicalORCSLPGFRows
    orcsLpgfRowCountField :
      orcsLpgfRowCount ≡ 8
    orcsLpgfSummary :
      String
    orcsLpgfSummaryIsCanonical :
      orcsLpgfSummary ≡ canonicalORCSLPGFSummary
    boundaryRecordedField :
      boundaryRecorded ≡ true
    estimateTargetRecordedField :
      estimateTargetRecorded ≡ true
    naiveRouteRecordedField :
      naiveRouteRecorded ≡ true
    tightEstimateProvedField :
      tightEstimateProved ≡ false
    clayNavierStokesPromotedField :
      clayNavierStokesPromoted ≡ false

open NSTriadicShellBernsteinHolderBoundary public

canonicalNSTriadicShellBernsteinHolderBoundary :
  NSTriadicShellBernsteinHolderBoundary
canonicalNSTriadicShellBernsteinHolderBoundary =
  nsTriadicShellBernsteinHolderBoundary
    "DASHI.Physics.Closure.NSTriadicShellBernsteinHolderBoundary"
    refl
    canonicalDyadicIndices
    refl
    refl
    canonicalLPShells
    refl
    refl
    canonicalTightTriadicShellEstimateTarget
    refl
    canonicalEstimateFactors
    refl
    refl
    canonicalNaiveBernsteinRoutes
    refl
    refl
    canonicalNaiveRouteInsufficiencies
    refl
    refl
    canonicalCoifmanMeyerNearDiagonalRoutes
    refl
    refl
    canonicalNSTriadicShellBernsteinHolderBlockers
    refl
    refl
    canonicalORCSLPGFRows
    refl
    refl
    canonicalORCSLPGFSummary
    refl
    refl
    refl
    refl
    refl
    refl
