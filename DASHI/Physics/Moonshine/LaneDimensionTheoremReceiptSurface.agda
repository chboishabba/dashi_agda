module DASHI.Physics.Moonshine.LaneDimensionTheoremReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Moonshine.DongLiMasonOrbifoldReceiptSurface as DLM
import DASHI.Physics.Moonshine.DASHIPrimeLaneEquivClosureReceiptSurface as BridgeClosure
import DASHI.Physics.Moonshine.PrimeLaneVOAEquivalenceReceiptSurface as Bridge
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as PrimeLane

------------------------------------------------------------------------
-- Lane-dimension theorem receipt surface.
--
-- This module is a composition surface only.  It connects the existing
-- Monster-prime lane table to an orbifold weight-1 Lie algebra rank table.
-- The named theorem is authority-backed and remains conditional after the
-- DASHIPrimeLaneEquiv closure receipt records the P2-A/P2-B/DLM inputs.  It
-- does not export a local lane-dimension theorem promotion, Clay mass-gap
-- promotion, or unguarded terminal claim.

data LaneDimensionTheoremSurfaceStatus : Set where
  conditionalReceiptOnlyNoUnconditionalPromotion :
    LaneDimensionTheoremSurfaceStatus

  authorityBackedNoLocalLaneDimensionPromotion :
    LaneDimensionTheoremSurfaceStatus

data LaneDimensionTheoremPromotionAuthorityToken : Set where

data DASHIPrimeLaneEquivStatus : Set where
  candidateDASHIPrimeLaneEquiv :
    DASHIPrimeLaneEquivStatus

data DLMOrbifoldAuthorityStatus : Set where
  externalDLMOrbifoldWeightOneLieRankAuthority :
    DLMOrbifoldAuthorityStatus

data LaneDimensionTheoremDependency : Set where
  dependsOnP2ADongLiMasonOrbifoldReceiptSurface :
    LaneDimensionTheoremDependency

  dependsOnP2BDASHIPrimeLaneEquivReceiptSurface :
    LaneDimensionTheoremDependency

  dependsOnCandidateDASHIPrimeLaneEquiv :
    LaneDimensionTheoremDependency

  dependsOnDLMOrbifoldAuthority :
    LaneDimensionTheoremDependency

  dependsOnDASHIPrimeLaneEquivClosureReceipt :
    LaneDimensionTheoremDependency

canonicalLaneDimensionTheoremDependencies :
  List LaneDimensionTheoremDependency
canonicalLaneDimensionTheoremDependencies =
  dependsOnP2ADongLiMasonOrbifoldReceiptSurface
  ∷ dependsOnP2BDASHIPrimeLaneEquivReceiptSurface
  ∷ dependsOnCandidateDASHIPrimeLaneEquiv
  ∷ dependsOnDLMOrbifoldAuthority
  ∷ dependsOnDASHIPrimeLaneEquivClosureReceipt
  ∷ []

dashiPrimeLaneEquivStatus :
  ((p : PrimeLane.MonsterPrimeLane) →
   Bridge.DASHIPrimeLaneEquiv p) →
  DASHIPrimeLaneEquivStatus
dashiPrimeLaneEquivStatus _ =
  candidateDASHIPrimeLaneEquiv

dlmAuthorityStatus :
  DLM.DongLiMasonOrbifoldReceiptSurface →
  DLMOrbifoldAuthorityStatus
dlmAuthorityStatus _ =
  externalDLMOrbifoldWeightOneLieRankAuthority

orbifoldWeightOneLieAlgebraRank :
  PrimeLane.MonsterPrimeLane →
  Nat
orbifoldWeightOneLieAlgebraRank PrimeLane.p2 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p3 =
  1
orbifoldWeightOneLieAlgebraRank PrimeLane.p5 =
  2
orbifoldWeightOneLieAlgebraRank PrimeLane.p7 =
  1
orbifoldWeightOneLieAlgebraRank PrimeLane.p11 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p13 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p17 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p19 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p23 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p29 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p31 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p41 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p47 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p59 =
  0
orbifoldWeightOneLieAlgebraRank PrimeLane.p71 =
  0

orbifoldWeightOneLieAlgebraDimension :
  PrimeLane.MonsterPrimeLane →
  Nat
orbifoldWeightOneLieAlgebraDimension PrimeLane.p2 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p3 =
  3
orbifoldWeightOneLieAlgebraDimension PrimeLane.p5 =
  8
orbifoldWeightOneLieAlgebraDimension PrimeLane.p7 =
  3
orbifoldWeightOneLieAlgebraDimension PrimeLane.p11 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p13 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p17 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p19 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p23 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p29 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p31 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p41 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p47 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p59 =
  0
orbifoldWeightOneLieAlgebraDimension PrimeLane.p71 =
  0

orbifoldLaneDimensionFromWeightOneLieAlgebra :
  PrimeLane.MonsterPrimeLane →
  Nat
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p2 =
  1
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p3 =
  2
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p5 =
  3
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p7 =
  2
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p11 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p13 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p17 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p19 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p23 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p29 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p31 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p41 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p47 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p59 =
  0
orbifoldLaneDimensionFromWeightOneLieAlgebra PrimeLane.p71 =
  0

laneDimensionTable :
  PrimeLane.MonsterPrimeLane →
  Nat
laneDimensionTable =
  PrimeLane.monsterPrimeLaneConjecturalDHRDimension

orbifoldLaneDimensionAgreesWithLaneDimensionTable :
  (p : PrimeLane.MonsterPrimeLane) →
  orbifoldLaneDimensionFromWeightOneLieAlgebra p ≡ laneDimensionTable p
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p2 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p3 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p5 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p7 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p11 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p13 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p17 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p19 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p23 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p29 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p31 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p41 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p47 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p59 =
  refl
orbifoldLaneDimensionAgreesWithLaneDimensionTable PrimeLane.p71 =
  refl

orbifoldRank2Is0 :
  orbifoldWeightOneLieAlgebraRank PrimeLane.p2 ≡ 0
orbifoldRank2Is0 =
  refl

orbifoldRank3Is1 :
  orbifoldWeightOneLieAlgebraRank PrimeLane.p3 ≡ 1
orbifoldRank3Is1 =
  refl

orbifoldRank5Is2 :
  orbifoldWeightOneLieAlgebraRank PrimeLane.p5 ≡ 2
orbifoldRank5Is2 =
  refl

orbifoldRank7Is1 :
  orbifoldWeightOneLieAlgebraRank PrimeLane.p7 ≡ 1
orbifoldRank7Is1 =
  refl

orbifoldRankAtLeast11Is0 :
  (p : PrimeLane.MonsterPrimeLane) →
  PrimeLane.MonsterPrimeLaneAtLeast11 p →
  orbifoldWeightOneLieAlgebraRank p ≡ 0
orbifoldRankAtLeast11Is0 PrimeLane.p11 PrimeLane.p11AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p13 PrimeLane.p13AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p17 PrimeLane.p17AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p19 PrimeLane.p19AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p23 PrimeLane.p23AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p29 PrimeLane.p29AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p31 PrimeLane.p31AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p41 PrimeLane.p41AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p47 PrimeLane.p47AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p59 PrimeLane.p59AtLeast11 =
  refl
orbifoldRankAtLeast11Is0 PrimeLane.p71 PrimeLane.p71AtLeast11 =
  refl

laneDimension2Is1 :
  laneDimensionTable PrimeLane.p2 ≡ 1
laneDimension2Is1 =
  refl

laneDimension3Is2 :
  laneDimensionTable PrimeLane.p3 ≡ 2
laneDimension3Is2 =
  refl

laneDimension5Is3 :
  laneDimensionTable PrimeLane.p5 ≡ 3
laneDimension5Is3 =
  refl

laneDimension7Is2 :
  laneDimensionTable PrimeLane.p7 ≡ 2
laneDimension7Is2 =
  refl

laneDimensionAtLeast11Is0 :
  (p : PrimeLane.MonsterPrimeLane) →
  PrimeLane.MonsterPrimeLaneAtLeast11 p →
  laneDimensionTable p ≡ 0
laneDimensionAtLeast11Is0 =
  PrimeLane.monsterPrimeLaneDHRDimensionAtLeast11Is0

record LaneDimensionTheoremReceipt : Setω where
  field
    receiptStatus :
      LaneDimensionTheoremSurfaceStatus

    dashiPrimeLaneEquiv :
      (p : PrimeLane.MonsterPrimeLane) →
      Bridge.DASHIPrimeLaneEquiv p

    dashiPrimeLaneEquivStatusField :
      DASHIPrimeLaneEquivStatus

    dashiPrimeLaneEquivStatusField-v :
      dashiPrimeLaneEquivStatusField
      ≡
      dashiPrimeLaneEquivStatus dashiPrimeLaneEquiv

    dlmOrbifoldAuthority :
      DLM.DongLiMasonOrbifoldReceiptSurface

    dashiPrimeLaneEquivClosure :
      BridgeClosure.DASHIPrimeLaneEquivClosureReceipt

    dlmOrbifoldAuthorityStatusField :
      DLMOrbifoldAuthorityStatus

    dlmOrbifoldAuthorityStatusField-v :
      dlmOrbifoldAuthorityStatusField
      ≡
      dlmAuthorityStatus dlmOrbifoldAuthority

    dependencies :
      List LaneDimensionTheoremDependency

    dependencies-v :
      dependencies
      ≡
      canonicalLaneDimensionTheoremDependencies

    p2ADongLiMasonSurfacePresent :
      Bool

    p2ADongLiMasonSurfacePresent-v :
      p2ADongLiMasonSurfacePresent ≡ true

    p2BDASHIPrimeLaneEquivSurfacePresent :
      Bool

    p2BDASHIPrimeLaneEquivSurfacePresent-v :
      p2BDASHIPrimeLaneEquivSurfacePresent ≡ true

    weightOneLieRank :
      PrimeLane.MonsterPrimeLane →
      Nat

    weightOneLieRank-v :
      weightOneLieRank
      ≡
      orbifoldWeightOneLieAlgebraRank

    weightOneLieDimension :
      PrimeLane.MonsterPrimeLane →
      Nat

    weightOneLieDimension-v :
      weightOneLieDimension
      ≡
      orbifoldWeightOneLieAlgebraDimension

    laneDimensionFromOrbifold :
      PrimeLane.MonsterPrimeLane →
      Nat

    laneDimensionFromOrbifold-v :
      laneDimensionFromOrbifold
      ≡
      orbifoldLaneDimensionFromWeightOneLieAlgebra

    laneDimension :
      PrimeLane.MonsterPrimeLane →
      Nat

    laneDimension-v :
      laneDimension
      ≡
      laneDimensionTable

    tableAgrees :
      (p : PrimeLane.MonsterPrimeLane) →
      laneDimensionFromOrbifold p ≡ laneDimension p

    rank2Is0 :
      weightOneLieRank PrimeLane.p2 ≡ 0

    rank3Is1 :
      weightOneLieRank PrimeLane.p3 ≡ 1

    rank5Is2 :
      weightOneLieRank PrimeLane.p5 ≡ 2

    rank7Is1 :
      weightOneLieRank PrimeLane.p7 ≡ 1

    rankAtLeast11Is0 :
      (p : PrimeLane.MonsterPrimeLane) →
      PrimeLane.MonsterPrimeLaneAtLeast11 p →
      weightOneLieRank p ≡ 0

    laneDimension2Is1Field :
      laneDimension PrimeLane.p2 ≡ 1

    laneDimension3Is2Field :
      laneDimension PrimeLane.p3 ≡ 2

    laneDimension5Is3Field :
      laneDimension PrimeLane.p5 ≡ 3

    laneDimension7Is2Field :
      laneDimension PrimeLane.p7 ≡ 2

    laneDimensionAtLeast11Is0Field :
      (p : PrimeLane.MonsterPrimeLane) →
      PrimeLane.MonsterPrimeLaneAtLeast11 p →
      laneDimension p ≡ 0

    theoremConditional :
      Bool

    theoremConditional-v :
      theoremConditional ≡ true

    unconditionalPromotion :
      Bool

    unconditionalPromotion-v :
      unconditionalPromotion ≡ false

    internalLaneDimensionPromotion :
      Bool

    internalLaneDimensionPromotion-v :
      internalLaneDimensionPromotion ≡ false

    terminalLaneDimensionPromotion :
      Bool

    terminalLaneDimensionPromotion-v :
      terminalLaneDimensionPromotion ≡ false

    clayLaneDimensionPromotion :
      Bool

    clayLaneDimensionPromotion-v :
      clayLaneDimensionPromotion ≡ false

    noPromotionWithoutAuthority :
      LaneDimensionTheoremPromotionAuthorityToken →
      ⊥

    theoremBoundary :
      List String

open LaneDimensionTheoremReceipt public

laneDimensionTheorem :
  ((p : PrimeLane.MonsterPrimeLane) →
   Bridge.DASHIPrimeLaneEquiv p) →
  DLM.DongLiMasonOrbifoldReceiptSurface →
  BridgeClosure.DASHIPrimeLaneEquivClosureReceipt →
  LaneDimensionTheoremReceipt
laneDimensionTheorem equiv dlm closure =
  record
    { receiptStatus =
        authorityBackedNoLocalLaneDimensionPromotion
    ; dashiPrimeLaneEquiv =
        equiv
    ; dashiPrimeLaneEquivStatusField =
        dashiPrimeLaneEquivStatus equiv
    ; dashiPrimeLaneEquivStatusField-v =
        refl
    ; dlmOrbifoldAuthority =
        dlm
    ; dashiPrimeLaneEquivClosure =
        closure
    ; dlmOrbifoldAuthorityStatusField =
        dlmAuthorityStatus dlm
    ; dlmOrbifoldAuthorityStatusField-v =
        refl
    ; dependencies =
        canonicalLaneDimensionTheoremDependencies
    ; dependencies-v =
        refl
    ; p2ADongLiMasonSurfacePresent =
        true
    ; p2ADongLiMasonSurfacePresent-v =
        refl
    ; p2BDASHIPrimeLaneEquivSurfacePresent =
        true
    ; p2BDASHIPrimeLaneEquivSurfacePresent-v =
        refl
    ; weightOneLieRank =
        orbifoldWeightOneLieAlgebraRank
    ; weightOneLieRank-v =
        refl
    ; weightOneLieDimension =
        orbifoldWeightOneLieAlgebraDimension
    ; weightOneLieDimension-v =
        refl
    ; laneDimensionFromOrbifold =
        orbifoldLaneDimensionFromWeightOneLieAlgebra
    ; laneDimensionFromOrbifold-v =
        refl
    ; laneDimension =
        laneDimensionTable
    ; laneDimension-v =
        refl
    ; tableAgrees =
        orbifoldLaneDimensionAgreesWithLaneDimensionTable
    ; rank2Is0 =
        refl
    ; rank3Is1 =
        refl
    ; rank5Is2 =
        refl
    ; rank7Is1 =
        refl
    ; rankAtLeast11Is0 =
        orbifoldRankAtLeast11Is0
    ; laneDimension2Is1Field =
        refl
    ; laneDimension3Is2Field =
        refl
    ; laneDimension5Is3Field =
        refl
    ; laneDimension7Is2Field =
        refl
    ; laneDimensionAtLeast11Is0Field =
        laneDimensionAtLeast11Is0
    ; theoremConditional =
        true
    ; theoremConditional-v =
        refl
    ; unconditionalPromotion =
        false
    ; unconditionalPromotion-v =
        refl
    ; internalLaneDimensionPromotion =
        BridgeClosure.laneDimensionPromotableFromClosure closure
    ; internalLaneDimensionPromotion-v =
        BridgeClosure.laneDimensionPromotableFromClosureIsFalse closure
    ; terminalLaneDimensionPromotion =
        false
    ; terminalLaneDimensionPromotion-v =
        refl
    ; clayLaneDimensionPromotion =
        false
    ; clayLaneDimensionPromotion-v =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; theoremBoundary =
        "laneDimensionTheorem records the DASHIPrimeLaneEquiv closure receipt as authority-backed input"
        ∷ "P2-A is represented by the DLM orbifold weight-1 Lie algebra authority surface"
        ∷ "P2-B is represented by the DASHIPrimeLaneEquiv closure receipt, with the original candidate surface retained as provenance"
        ∷ "laneDimensionTheorem also requires DLM orbifold weight-1 Lie algebra rank authority"
        ∷ "orbifold weight-1 Lie algebra dimension table is wired as 2->0, 3->3, 5->8, 7->3, primes >=11 -> 0"
        ∷ "rank table is 2->0, 3->1, 5->2, 7->1, and the lane-dimension table is 2->1, 3->2, 5->3, 7->2, primes >=11 -> 0"
        ∷ "P2-A/P2-B/DLM closure does not promote laneDimension without a separate promotion authority"
        ∷ "the lane-dimension table reuses the existing conjectural Monster-prime DHR dimension table"
        ∷ "no Clay mass-gap promotion or unguarded terminal-claim promotion is exported by this surface"
        ∷ []
    }

canonicalLaneDimensionTheoremReceipt :
  LaneDimensionTheoremReceipt
canonicalLaneDimensionTheoremReceipt =
  laneDimensionTheorem
    Bridge.canonicalDASHIPrimeLaneEquiv
    DLM.canonicalDongLiMasonOrbifoldReceiptSurface
    BridgeClosure.canonicalDASHIPrimeLaneEquivClosureReceipt

laneDimensionPromoted :
  Bool
laneDimensionPromoted =
  false

laneDimensionPromotedIsFalse :
  laneDimensionPromoted ≡ false
laneDimensionPromotedIsFalse =
  refl

laneDimensionInternalPromoted :
  Bool
laneDimensionInternalPromoted =
  laneDimensionPromoted

laneDimensionInternalPromotedIsFalse :
  laneDimensionInternalPromoted ≡ false
laneDimensionInternalPromotedIsFalse =
  refl

laneDimensionTerminalPromoted :
  Bool
laneDimensionTerminalPromoted =
  false

laneDimensionTerminalPromotedIsFalse :
  laneDimensionTerminalPromoted ≡ false
laneDimensionTerminalPromotedIsFalse =
  refl

laneDimensionClayPromoted :
  Bool
laneDimensionClayPromoted =
  false

laneDimensionClayPromotedIsFalse :
  laneDimensionClayPromoted ≡ false
laneDimensionClayPromotedIsFalse =
  refl
