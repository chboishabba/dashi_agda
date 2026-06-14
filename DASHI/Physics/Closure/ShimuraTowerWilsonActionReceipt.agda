module DASHI.Physics.Closure.ShimuraTowerWilsonActionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

data ShimuraTowerWilsonActionStatus : Set where
  shimuraTowerWilsonActionRecordedNoClayPromotion :
    ShimuraTowerWilsonActionStatus

data ModularCurveTower : Set where
  X0-3^k :
    ModularCurveTower

  X0-4^k :
    ModularCurveTower

  X0-7^k :
    ModularCurveTower

canonicalShimuraTowerLevels :
  List ModularCurveTower
canonicalShimuraTowerLevels =
  X0-3^k
  ∷ X0-4^k
  ∷ X0-7^k
  ∷ []

data ShimuraTowerPointKind : Set where
  cmPointOfX0-3^k :
    ShimuraTowerPointKind

  cmPointOfX0-4^k :
    ShimuraTowerPointKind

  cmPointOfX0-7^k :
    ShimuraTowerPointKind

canonicalShimuraTowerPointKinds :
  List ShimuraTowerPointKind
canonicalShimuraTowerPointKinds =
  cmPointOfX0-3^k
  ∷ cmPointOfX0-4^k
  ∷ cmPointOfX0-7^k
  ∷ []

data ShimuraTowerLinkKind : Set where
  heckeCorrespondenceConnectedPair :
    ShimuraTowerLinkKind

canonicalShimuraTowerLinkKinds :
  List ShimuraTowerLinkKind
canonicalShimuraTowerLinkKinds =
  heckeCorrespondenceConnectedPair
  ∷ []

data ShimuraTowerPlaquetteKind : Set where
  heckeOrbitQuadrilateral :
    ShimuraTowerPlaquetteKind

canonicalShimuraTowerPlaquetteKinds :
  List ShimuraTowerPlaquetteKind
canonicalShimuraTowerPlaquetteKinds =
  heckeOrbitQuadrilateral
  ∷ []

data ReflectionPositivityInheritanceStatus : Set where
  candidate :
    ReflectionPositivityInheritanceStatus

  inheritedTrue :
    ReflectionPositivityInheritanceStatus

data ShimuraTowerWilsonActionBlocker : Set where
  reflectionPositivityOnlyCandidate :
    ShimuraTowerWilsonActionBlocker

  missingContinuumLimit :
    ShimuraTowerWilsonActionBlocker

  missingUniformMassGap :
    ShimuraTowerWilsonActionBlocker

  missingExternalClayAuthority :
    ShimuraTowerWilsonActionBlocker

canonicalShimuraTowerWilsonActionBlockers :
  List ShimuraTowerWilsonActionBlocker
canonicalShimuraTowerWilsonActionBlockers =
  reflectionPositivityOnlyCandidate
  ∷ missingContinuumLimit
  ∷ missingUniformMassGap
  ∷ missingExternalClayAuthority
  ∷ []

data ShimuraTowerClayPromotion : Set where

shimuraTowerClayPromotionImpossibleHere :
  ShimuraTowerClayPromotion →
  ⊥
shimuraTowerClayPromotionImpossibleHere ()

shimuraTowerLabel : String
shimuraTowerLabel =
  "Shimura tower lattice with levels X0(3^k), X0(4^k), and X0(7^k)"

cmPointLevelLabel : String
cmPointLevelLabel =
  "At each level k, the sites are CM points of X0(3^k), X0(4^k), and X0(7^k)"

heckeCorrespondenceLabel : String
heckeCorrespondenceLabel =
  "Hecke correspondences T_p connect CM points; links are Hecke-correspondence-connected pairs"

heckePlaquetteLabel : String
heckePlaquetteLabel =
  "Plaquettes are quadrilaterals formed by four CM points in a Hecke orbit"

shimuraTowerWilsonActionLabel : String
shimuraTowerWilsonActionLabel =
  "S_k[U] = -(beta/2N) sum_square Re Tr(U_square)"

reflectionPositivityCandidateLabel : String
reflectionPositivityCandidateLabel =
  "reflection positivity is inherited/candidate because the Hecke correspondences are real and reflection-compatible"

record ShimuraTowerWilsonActionReceipt : Setω where
  field
    status :
      ShimuraTowerWilsonActionStatus

    latticeLabel :
      String

    latticeLabelIsCanonical :
      latticeLabel ≡ shimuraTowerLabel

    levelIndex :
      Nat

    levels :
      List ModularCurveTower

    levelsAreCanonical :
      levels ≡ canonicalShimuraTowerLevels

    pointKinds :
      List ShimuraTowerPointKind

    pointKindsAreCanonical :
      pointKinds ≡ canonicalShimuraTowerPointKinds

    cmPointsAtEachLevel :
      Bool

    cmPointsAtEachLevelIsTrue :
      cmPointsAtEachLevel ≡ true

    cmPointLevelStatement :
      String

    cmPointLevelStatementIsCanonical :
      cmPointLevelStatement ≡ cmPointLevelLabel

    heckeCorrespondencesTp :
      Bool

    heckeCorrespondencesTpIsTrue :
      heckeCorrespondencesTp ≡ true

    heckeCorrespondenceStatement :
      String

    heckeCorrespondenceStatementIsCanonical :
      heckeCorrespondenceStatement ≡ heckeCorrespondenceLabel

    linkKinds :
      List ShimuraTowerLinkKind

    linkKindsAreCanonical :
      linkKinds ≡ canonicalShimuraTowerLinkKinds

    linksAreHeckeCorrespondenceConnectedPairs :
      Bool

    linksAreHeckeCorrespondenceConnectedPairsIsTrue :
      linksAreHeckeCorrespondenceConnectedPairs ≡ true

    plaquetteKinds :
      List ShimuraTowerPlaquetteKind

    plaquetteKindsAreCanonical :
      plaquetteKinds ≡ canonicalShimuraTowerPlaquetteKinds

    plaquettesFromHeckeOrbits :
      Bool

    plaquettesFromHeckeOrbitsIsTrue :
      plaquettesFromHeckeOrbits ≡ true

    plaquetteStatement :
      String

    plaquetteStatementIsCanonical :
      plaquetteStatement ≡ heckePlaquetteLabel

    betaSymbol :
      String

    betaSymbolIsCanonical :
      betaSymbol ≡ "beta"

    gaugeRankSymbol :
      String

    gaugeRankSymbolIsCanonical :
      gaugeRankSymbol ≡ "N"

    wilsonActionStatement :
      String

    wilsonActionStatementIsCanonical :
      wilsonActionStatement ≡ shimuraTowerWilsonActionLabel

    shimuraTowerWilsonActionDefined :
      Bool

    shimuraTowerWilsonActionDefinedIsTrue :
      shimuraTowerWilsonActionDefined ≡ true

    heckeCorrespondencesReal :
      Bool

    heckeCorrespondencesRealIsTrue :
      heckeCorrespondencesReal ≡ true

    heckeCorrespondencesReflectionCompatible :
      Bool

    heckeCorrespondencesReflectionCompatibleIsTrue :
      heckeCorrespondencesReflectionCompatible ≡ true

    reflectionPositivityInherited :
      ReflectionPositivityInheritanceStatus

    reflectionPositivityInheritedIsCandidate :
      reflectionPositivityInherited ≡ candidate

    reflectionPositivityStatement :
      String

    reflectionPositivityStatementIsCanonical :
      reflectionPositivityStatement ≡ reflectionPositivityCandidateLabel

    reflectionPositivityPromotedToTheorem :
      Bool

    reflectionPositivityPromotedToTheoremIsFalse :
      reflectionPositivityPromotedToTheorem ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    blockers :
      List ShimuraTowerWilsonActionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalShimuraTowerWilsonActionBlockers

    promotionFlags :
      List ShimuraTowerClayPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ShimuraTowerWilsonActionReceipt public

canonicalShimuraTowerWilsonActionReceipt :
  ShimuraTowerWilsonActionReceipt
canonicalShimuraTowerWilsonActionReceipt =
  record
    { status =
        shimuraTowerWilsonActionRecordedNoClayPromotion
    ; latticeLabel =
        shimuraTowerLabel
    ; latticeLabelIsCanonical =
        refl
    ; levelIndex =
        0
    ; levels =
        canonicalShimuraTowerLevels
    ; levelsAreCanonical =
        refl
    ; pointKinds =
        canonicalShimuraTowerPointKinds
    ; pointKindsAreCanonical =
        refl
    ; cmPointsAtEachLevel =
        true
    ; cmPointsAtEachLevelIsTrue =
        refl
    ; cmPointLevelStatement =
        cmPointLevelLabel
    ; cmPointLevelStatementIsCanonical =
        refl
    ; heckeCorrespondencesTp =
        true
    ; heckeCorrespondencesTpIsTrue =
        refl
    ; heckeCorrespondenceStatement =
        heckeCorrespondenceLabel
    ; heckeCorrespondenceStatementIsCanonical =
        refl
    ; linkKinds =
        canonicalShimuraTowerLinkKinds
    ; linkKindsAreCanonical =
        refl
    ; linksAreHeckeCorrespondenceConnectedPairs =
        true
    ; linksAreHeckeCorrespondenceConnectedPairsIsTrue =
        refl
    ; plaquetteKinds =
        canonicalShimuraTowerPlaquetteKinds
    ; plaquetteKindsAreCanonical =
        refl
    ; plaquettesFromHeckeOrbits =
        true
    ; plaquettesFromHeckeOrbitsIsTrue =
        refl
    ; plaquetteStatement =
        heckePlaquetteLabel
    ; plaquetteStatementIsCanonical =
        refl
    ; betaSymbol =
        "beta"
    ; betaSymbolIsCanonical =
        refl
    ; gaugeRankSymbol =
        "N"
    ; gaugeRankSymbolIsCanonical =
        refl
    ; wilsonActionStatement =
        shimuraTowerWilsonActionLabel
    ; wilsonActionStatementIsCanonical =
        refl
    ; shimuraTowerWilsonActionDefined =
        true
    ; shimuraTowerWilsonActionDefinedIsTrue =
        refl
    ; heckeCorrespondencesReal =
        true
    ; heckeCorrespondencesRealIsTrue =
        refl
    ; heckeCorrespondencesReflectionCompatible =
        true
    ; heckeCorrespondencesReflectionCompatibleIsTrue =
        refl
    ; reflectionPositivityInherited =
        candidate
    ; reflectionPositivityInheritedIsCandidate =
        refl
    ; reflectionPositivityStatement =
        reflectionPositivityCandidateLabel
    ; reflectionPositivityStatementIsCanonical =
        refl
    ; reflectionPositivityPromotedToTheorem =
        false
    ; reflectionPositivityPromotedToTheoremIsFalse =
        refl
    ; continuumYangMillsConstructed =
        true
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
    ; blockers =
        canonicalShimuraTowerWilsonActionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records a finite-level Wilson action on the Shimura tower lattice"
        ∷ "At each level k, CM points of X0(3^k), X0(4^k), and X0(7^k) are connected by Hecke correspondences T_p"
        ∷ "Links are Hecke-correspondence-connected pairs"
        ∷ "Plaquettes are quadrilaterals formed by four CM points in a Hecke orbit"
        ∷ "The finite action is S_k = -(beta/2N) sum_square Re Tr(U_square)"
        ∷ "Reflection positivity is recorded only as inherited/candidate from real reflection-compatible correspondences"
        ∷ "No continuum Yang-Mills, Clay Yang-Mills, or terminal Clay promotion is made"
        ∷ []
    }

shimuraTowerWilsonActionDefinedFlag :
  shimuraTowerWilsonActionDefined canonicalShimuraTowerWilsonActionReceipt
  ≡
  true
shimuraTowerWilsonActionDefinedFlag =
  refl

plaquettesFromHeckeOrbitsFlag :
  plaquettesFromHeckeOrbits canonicalShimuraTowerWilsonActionReceipt
  ≡
  true
plaquettesFromHeckeOrbitsFlag =
  refl

reflectionPositivityInheritedCandidateFlag :
  reflectionPositivityInherited canonicalShimuraTowerWilsonActionReceipt
  ≡
  candidate
reflectionPositivityInheritedCandidateFlag =
  refl

shimuraTowerWilsonActionDoesNotPromoteClay :
  clayYangMillsPromoted canonicalShimuraTowerWilsonActionReceipt
  ≡
  false
shimuraTowerWilsonActionDoesNotPromoteClay =
  refl

shimuraTowerWilsonActionDoesNotPromoteTerminalClay :
  terminalClayClaimPromoted canonicalShimuraTowerWilsonActionReceipt
  ≡
  false
shimuraTowerWilsonActionDoesNotPromoteTerminalClay =
  refl
