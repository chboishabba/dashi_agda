module DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Moonshine
import DASHI.Physics.QFT.DHRSectorDecomposition as DHR
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM

------------------------------------------------------------------------
-- Concrete finite prime-lane / DHR-SM compatibility ledger.
--
-- This ledger is deliberately finite.  It records the existing p2/p3/p5
-- evidence as prime-lane assignments into the current DHR sector-decomposition
-- witnesses.  It does not construct arbitrary DHR endomorphism categories,
-- lane-wise representation equivalences, DR reconstruction, or G_DHR ~= G_SM.

data PrimeLaneSMGaugeFactor : Set where
  U1Y :
    PrimeLaneSMGaugeFactor

  SU2L :
    PrimeLaneSMGaugeFactor

  SU3c :
    PrimeLaneSMGaugeFactor

primeLaneSMGaugeDimension :
  PrimeLaneSMGaugeFactor →
  Nat
primeLaneSMGaugeDimension U1Y =
  1
primeLaneSMGaugeDimension SU2L =
  2
primeLaneSMGaugeDimension SU3c =
  3

data FinitePrimeLaneSMRowKind : Set where
  p2U1YRow :
    FinitePrimeLaneSMRowKind

  p3SU2LRow :
    FinitePrimeLaneSMRowKind

  p5SU3cRow :
    FinitePrimeLaneSMRowKind

record FinitePrimeLaneSMRow : Set where
  field
    rowKind :
      FinitePrimeLaneSMRowKind

    primeLane :
      Moonshine.MonsterPrimeLane

    gaugeFactor :
      PrimeLaneSMGaugeFactor

    gaugeDimension :
      Nat

    gaugeDimensionMatchesFactor :
      gaugeDimension ≡ primeLaneSMGaugeDimension gaugeFactor

    moonshineDimension :
      Moonshine.monsterPrimeLaneConjecturalDHRDimension primeLane
      ≡
      gaugeDimension

    sectorAtom :
      DHR.DHRGaugeSectorAtom

    rowBoundary :
      List String

open FinitePrimeLaneSMRow public

p2U1YFinitePrimeLaneSMRow :
  FinitePrimeLaneSMRow
p2U1YFinitePrimeLaneSMRow =
  record
    { rowKind =
        p2U1YRow
    ; primeLane =
        Moonshine.p2
    ; gaugeFactor =
        U1Y
    ; gaugeDimension =
        1
    ; gaugeDimensionMatchesFactor =
        refl
    ; moonshineDimension =
        refl
    ; sectorAtom =
        DHR.U1Sector
    ; rowBoundary =
        "p2 is assigned to U1Y with finite lane dimension 1"
        ∷ "The row consumes the current DHR U1 sector atom only"
        ∷ []
    }

p3SU2LFinitePrimeLaneSMRow :
  FinitePrimeLaneSMRow
p3SU2LFinitePrimeLaneSMRow =
  record
    { rowKind =
        p3SU2LRow
    ; primeLane =
        Moonshine.p3
    ; gaugeFactor =
        SU2L
    ; gaugeDimension =
        2
    ; gaugeDimensionMatchesFactor =
        refl
    ; moonshineDimension =
        refl
    ; sectorAtom =
        DHR.SU2Sector
    ; rowBoundary =
        "p3 is assigned to SU2L with finite lane dimension 2"
        ∷ "The row consumes the current DHR SU2 sector atom only"
        ∷ []
    }

p5SU3cFinitePrimeLaneSMRow :
  FinitePrimeLaneSMRow
p5SU3cFinitePrimeLaneSMRow =
  record
    { rowKind =
        p5SU3cRow
    ; primeLane =
        Moonshine.p5
    ; gaugeFactor =
        SU3c
    ; gaugeDimension =
        3
    ; gaugeDimensionMatchesFactor =
        refl
    ; moonshineDimension =
        refl
    ; sectorAtom =
        DHR.SU3Frontier
    ; rowBoundary =
        "p5 is assigned to SU3c with finite lane dimension 3"
        ∷ "The row consumes the current DHR SU3 frontier atom only"
        ∷ []
    }

canonicalFinitePrimeLaneSMRows :
  List FinitePrimeLaneSMRow
canonicalFinitePrimeLaneSMRows =
  p2U1YFinitePrimeLaneSMRow
  ∷ p3SU2LFinitePrimeLaneSMRow
  ∷ p5SU3cFinitePrimeLaneSMRow
  ∷ []

data FinitePrimeLaneDHRArrow :
  FinitePrimeLaneSMRow →
  FinitePrimeLaneSMRow →
  Set where
  finitePrimeLaneId :
    (row : FinitePrimeLaneSMRow) →
    FinitePrimeLaneDHRArrow row row

  finitePrimeLaneCompose :
    {x y z : FinitePrimeLaneSMRow} →
    FinitePrimeLaneDHRArrow y z →
    FinitePrimeLaneDHRArrow x y →
    FinitePrimeLaneDHRArrow x z

finitePrimeLaneDHRCompose :
  {x y z : FinitePrimeLaneSMRow} →
  FinitePrimeLaneDHRArrow y z →
  FinitePrimeLaneDHRArrow x y →
  FinitePrimeLaneDHRArrow x z
finitePrimeLaneDHRCompose (finitePrimeLaneId _) f =
  f
finitePrimeLaneDHRCompose g (finitePrimeLaneId _) =
  g
finitePrimeLaneDHRCompose g f =
  finitePrimeLaneCompose g f

finitePrimeLaneDHRLeftIdentity :
  {x y : FinitePrimeLaneSMRow} →
  (f : FinitePrimeLaneDHRArrow x y) →
  finitePrimeLaneDHRCompose (finitePrimeLaneId y) f ≡ f
finitePrimeLaneDHRLeftIdentity f =
  refl

finitePrimeLaneDHRRightIdentity :
  {x y : FinitePrimeLaneSMRow} →
  (f : FinitePrimeLaneDHRArrow x y) →
  finitePrimeLaneDHRCompose f (finitePrimeLaneId x) ≡ f
finitePrimeLaneDHRRightIdentity (finitePrimeLaneId _) =
  refl
finitePrimeLaneDHRRightIdentity (finitePrimeLaneCompose _ _) =
  refl

record FinitePrimeLaneDHRSMNaturalityReceipt : Setω where
  field
    p2Row :
      FinitePrimeLaneSMRow

    p2RowIsCanonical :
      p2Row ≡ p2U1YFinitePrimeLaneSMRow

    p3Row :
      FinitePrimeLaneSMRow

    p3RowIsCanonical :
      p3Row ≡ p3SU2LFinitePrimeLaneSMRow

    p5Row :
      FinitePrimeLaneSMRow

    p5RowIsCanonical :
      p5Row ≡ p5SU3cFinitePrimeLaneSMRow

    p2Identity :
      FinitePrimeLaneDHRArrow p2Row p2Row

    p2IdentityIsCanonical :
      p2Identity ≡ finitePrimeLaneId p2Row

    p3Identity :
      FinitePrimeLaneDHRArrow p3Row p3Row

    p3IdentityIsCanonical :
      p3Identity ≡ finitePrimeLaneId p3Row

    p5Identity :
      FinitePrimeLaneDHRArrow p5Row p5Row

    p5IdentityIsCanonical :
      p5Identity ≡ finitePrimeLaneId p5Row

    p2LeftIdentity :
      finitePrimeLaneDHRCompose p2Identity p2Identity
      ≡
      p2Identity

    p3LeftIdentity :
      finitePrimeLaneDHRCompose p3Identity p3Identity
      ≡
      p3Identity

    p5LeftIdentity :
      finitePrimeLaneDHRCompose p5Identity p5Identity
      ≡
      p5Identity

    identityReceiptsAvailable :
      Bool

    identityReceiptsAvailableIsTrue :
      identityReceiptsAvailable ≡ true

    compositionReceiptsAvailable :
      Bool

    compositionReceiptsAvailableIsTrue :
      compositionReceiptsAvailable ≡ true

    naturalityReceiptsAvailable :
      Bool

    naturalityReceiptsAvailableIsTrue :
      naturalityReceiptsAvailable ≡ true

    arbitrarySectorNaturalityPromoted :
      Bool

    arbitrarySectorNaturalityPromotedIsFalse :
      arbitrarySectorNaturalityPromoted ≡ false

    naturalityBoundary :
      List String

open FinitePrimeLaneDHRSMNaturalityReceipt public

canonicalFinitePrimeLaneDHRSMNaturalityReceipt :
  FinitePrimeLaneDHRSMNaturalityReceipt
canonicalFinitePrimeLaneDHRSMNaturalityReceipt =
  record
    { p2Row =
        p2U1YFinitePrimeLaneSMRow
    ; p2RowIsCanonical =
        refl
    ; p3Row =
        p3SU2LFinitePrimeLaneSMRow
    ; p3RowIsCanonical =
        refl
    ; p5Row =
        p5SU3cFinitePrimeLaneSMRow
    ; p5RowIsCanonical =
        refl
    ; p2Identity =
        finitePrimeLaneId p2U1YFinitePrimeLaneSMRow
    ; p2IdentityIsCanonical =
        refl
    ; p3Identity =
        finitePrimeLaneId p3SU2LFinitePrimeLaneSMRow
    ; p3IdentityIsCanonical =
        refl
    ; p5Identity =
        finitePrimeLaneId p5SU3cFinitePrimeLaneSMRow
    ; p5IdentityIsCanonical =
        refl
    ; p2LeftIdentity =
        refl
    ; p3LeftIdentity =
        refl
    ; p5LeftIdentity =
        refl
    ; identityReceiptsAvailable =
        true
    ; identityReceiptsAvailableIsTrue =
        refl
    ; compositionReceiptsAvailable =
        true
    ; compositionReceiptsAvailableIsTrue =
        refl
    ; naturalityReceiptsAvailable =
        true
    ; naturalityReceiptsAvailableIsTrue =
        refl
    ; arbitrarySectorNaturalityPromoted =
        false
    ; arbitrarySectorNaturalityPromotedIsFalse =
        refl
    ; naturalityBoundary =
        "Finite p2/p3/p5 identity and identity-composition receipts are reflexive over the ledger rows"
        ∷ "Naturality is finite-row naturality only: each row is threaded unchanged into its DHR sector atom"
        ∷ "No arbitrary-sector transport naturality theorem is promoted"
        ∷ []
    }

data PrimeLaneEndRepExactMatchBlocker : Set where
  missingPrimeLaneLocalAlgebraEndomorphismCategory :
    PrimeLaneEndRepExactMatchBlocker

  missingPrimeLaneCompactGroupConstruction :
    PrimeLaneEndRepExactMatchBlocker

  missingEndRhoPkToRepGPkEquivalence :
    PrimeLaneEndRepExactMatchBlocker

  missingLanewiseFaithfulnessAndKernelDecision :
    PrimeLaneEndRepExactMatchBlocker

canonicalPrimeLaneEndRepExactMatchBlockers :
  List PrimeLaneEndRepExactMatchBlocker
canonicalPrimeLaneEndRepExactMatchBlockers =
  missingPrimeLaneLocalAlgebraEndomorphismCategory
  ∷ missingPrimeLaneCompactGroupConstruction
  ∷ missingEndRhoPkToRepGPkEquivalence
  ∷ missingLanewiseFaithfulnessAndKernelDecision
  ∷ []

record PrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt : Setω where
  field
    exactTargetName :
      String

    exactTargetName-v :
      exactTargetName ≡ "End(rho_pk) ~= Rep(G_pk)"

    blockers :
      List PrimeLaneEndRepExactMatchBlocker

    blockersAreCanonical :
      blockers ≡ canonicalPrimeLaneEndRepExactMatchBlockers

    firstBlocker :
      PrimeLaneEndRepExactMatchBlocker

    firstBlockerIsLocalAlgebraEndomorphismCategory :
      firstBlocker
      ≡
      missingPrimeLaneLocalAlgebraEndomorphismCategory

    endRhoPkCategoryConstructed :
      Bool

    endRhoPkCategoryConstructedIsFalse :
      endRhoPkCategoryConstructed ≡ false

    repGPkConstructed :
      Bool

    repGPkConstructedIsFalse :
      repGPkConstructed ≡ false

    endRhoPkRepGPkEquivalenceConstructed :
      Bool

    endRhoPkRepGPkEquivalenceConstructedIsFalse :
      endRhoPkRepGPkEquivalenceConstructed ≡ false

    exactLaneMatchPromoted :
      Bool

    exactLaneMatchPromotedIsFalse :
      exactLaneMatchPromoted ≡ false

    blockerBoundary :
      List String

open PrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt public

canonicalPrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt :
  PrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt
canonicalPrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt =
  record
    { exactTargetName =
        "End(rho_pk) ~= Rep(G_pk)"
    ; exactTargetName-v =
        refl
    ; blockers =
        canonicalPrimeLaneEndRepExactMatchBlockers
    ; blockersAreCanonical =
        refl
    ; firstBlocker =
        missingPrimeLaneLocalAlgebraEndomorphismCategory
    ; firstBlockerIsLocalAlgebraEndomorphismCategory =
        refl
    ; endRhoPkCategoryConstructed =
        false
    ; endRhoPkCategoryConstructedIsFalse =
        refl
    ; repGPkConstructed =
        false
    ; repGPkConstructedIsFalse =
        refl
    ; endRhoPkRepGPkEquivalenceConstructed =
        false
    ; endRhoPkRepGPkEquivalenceConstructedIsFalse =
        refl
    ; exactLaneMatchPromoted =
        false
    ; exactLaneMatchPromotedIsFalse =
        refl
    ; blockerBoundary =
        "The exact lane target is End(rho_pk) ~= Rep(G_pk)"
        ∷ "The current finite rows do not construct the lane-local DHR endomorphism category"
        ∷ "They also do not construct G_pk, Rep(G_pk), the equivalence, faithfulness, or a kernel decision"
        ∷ []
    }

record FinitePrimeLaneDHRSMCompatibilityLedger : Setω where
  field
    dhrSectorDecomposition :
      DHR.DHRSectorDecomposition

    exactSMBlockerReceipt :
      ExactSM.ExactSMMatchBlockerReceipt

    rows :
      List FinitePrimeLaneSMRow

    rowsAreCanonical :
      rows ≡ canonicalFinitePrimeLaneSMRows

    p2Row :
      FinitePrimeLaneSMRow

    p2RowIsCanonical :
      p2Row ≡ p2U1YFinitePrimeLaneSMRow

    p3Row :
      FinitePrimeLaneSMRow

    p3RowIsCanonical :
      p3Row ≡ p3SU2LFinitePrimeLaneSMRow

    p5Row :
      FinitePrimeLaneSMRow

    p5RowIsCanonical :
      p5Row ≡ p5SU3cFinitePrimeLaneSMRow

    p2SectorMatchesDecomposition :
      DHR.DHRSectorDecomposition.u1SectorObject dhrSectorDecomposition
      ≡
      DHR.canonicalU1SectorObject

    p3SectorMatchesDecomposition :
      DHR.DHRSectorDecomposition.su2SectorObject dhrSectorDecomposition
      ≡
      DHR.canonicalSU2SectorObject

    p5FrontierThreadedFromDecomposition :
      Bool

    p5FrontierThreadedFromDecompositionIsTrue :
      p5FrontierThreadedFromDecomposition ≡ true

    finiteNaturality :
      FinitePrimeLaneDHRSMNaturalityReceipt

    endRhoPkRepGPkBlocker :
      PrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt

    finiteAssignmentsRecorded :
      Bool

    finiteAssignmentsRecordedIsTrue :
      finiteAssignmentsRecorded ≡ true

    exactGate1Gate6MatchPromoted :
      Bool

    exactGate1Gate6MatchPromotedIsFalse :
      exactGate1Gate6MatchPromoted ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    ledgerBoundary :
      List String

open FinitePrimeLaneDHRSMCompatibilityLedger public

canonicalFinitePrimeLaneDHRSMCompatibilityLedger :
  FinitePrimeLaneDHRSMCompatibilityLedger
canonicalFinitePrimeLaneDHRSMCompatibilityLedger =
  record
    { dhrSectorDecomposition =
        DHR.canonicalDHRSectorDecomposition
    ; exactSMBlockerReceipt =
        ExactSM.canonicalExactSMMatchBlockerReceipt
    ; rows =
        canonicalFinitePrimeLaneSMRows
    ; rowsAreCanonical =
        refl
    ; p2Row =
        p2U1YFinitePrimeLaneSMRow
    ; p2RowIsCanonical =
        refl
    ; p3Row =
        p3SU2LFinitePrimeLaneSMRow
    ; p3RowIsCanonical =
        refl
    ; p5Row =
        p5SU3cFinitePrimeLaneSMRow
    ; p5RowIsCanonical =
        refl
    ; p2SectorMatchesDecomposition =
        refl
    ; p3SectorMatchesDecomposition =
        refl
    ; p5FrontierThreadedFromDecomposition =
        true
    ; p5FrontierThreadedFromDecompositionIsTrue =
        refl
    ; finiteNaturality =
        canonicalFinitePrimeLaneDHRSMNaturalityReceipt
    ; endRhoPkRepGPkBlocker =
        canonicalPrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt
    ; finiteAssignmentsRecorded =
        true
    ; finiteAssignmentsRecordedIsTrue =
        refl
    ; exactGate1Gate6MatchPromoted =
        false
    ; exactGate1Gate6MatchPromotedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; ledgerBoundary =
        "Concrete finite ledger records p2->U1Y, p3->SU2L, and p5->SU3c"
        ∷ "The rows are checked against the current DHR U1, SU2, and SU3-frontier sector decomposition"
        ∷ "Finite identity, identity-composition, and row-naturality receipts are inhabited"
        ∷ "Exact End(rho_pk) ~= Rep(G_pk), Gate1/Gate6 exact match, and G_DHR ~= G_SM remain explicitly false promotions"
        ∷ []
    }
