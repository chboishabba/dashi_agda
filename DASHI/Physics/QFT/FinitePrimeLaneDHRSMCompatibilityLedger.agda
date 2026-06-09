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
import DASHI.Physics.QFT.W3ClockShiftAlgebra as W3
import DASHI.Physics.QFT.W3ToM3Iso as W3Iso
import DASHI.Physics.SFGC.NonAbelian.CliffordToM2Iso as CliffordM2
import DASHI.Physics.Closure.TriadicMatrixGenerationTheorem as TMG

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

data EndSectorMatrixTarget : Set where
  targetEndSectorC :
    EndSectorMatrixTarget

  targetEndSectorM2 :
    EndSectorMatrixTarget

  targetEndSectorM3 :
    EndSectorMatrixTarget

endSectorMatrixTargetSize :
  EndSectorMatrixTarget →
  Nat
endSectorMatrixTargetSize targetEndSectorC =
  1
endSectorMatrixTargetSize targetEndSectorM2 =
  2
endSectorMatrixTargetSize targetEndSectorM3 =
  3

record FinitePrimeLaneEndSectorMatrixTargetRow : Set where
  field
    finiteRow :
      FinitePrimeLaneSMRow

    targetAlgebra :
      EndSectorMatrixTarget

    matrixSize :
      Nat

    matrixSizeMatchesTarget :
      matrixSize ≡ endSectorMatrixTargetSize targetAlgebra

    laneDimensionMatchesMatrixSize :
      Moonshine.monsterPrimeLaneConjecturalDHRDimension
        (FinitePrimeLaneSMRow.primeLane finiteRow)
      ≡
      matrixSize

    sectorAtom :
      DHR.DHRGaugeSectorAtom

    sectorAtomMatchesFiniteRow :
      sectorAtom ≡ FinitePrimeLaneSMRow.sectorAtom finiteRow

    targetBoundary :
      List String

open FinitePrimeLaneEndSectorMatrixTargetRow public

p2CEndSectorMatrixTargetRow :
  FinitePrimeLaneEndSectorMatrixTargetRow
p2CEndSectorMatrixTargetRow =
  record
    { finiteRow =
        p2U1YFinitePrimeLaneSMRow
    ; targetAlgebra =
        targetEndSectorC
    ; matrixSize =
        1
    ; matrixSizeMatchesTarget =
        refl
    ; laneDimensionMatchesMatrixSize =
        refl
    ; sectorAtom =
        DHR.U1Sector
    ; sectorAtomMatchesFiniteRow =
        refl
    ; targetBoundary =
        "p2 targets EndSector(C) by dimension-1 row evidence and the current U1 sector atom"
        ∷ "No complex scalar carrier or DHR endomorphism algebra multiplication is constructed"
        ∷ []
    }

p3M2EndSectorMatrixTargetRow :
  FinitePrimeLaneEndSectorMatrixTargetRow
p3M2EndSectorMatrixTargetRow =
  record
    { finiteRow =
        p3SU2LFinitePrimeLaneSMRow
    ; targetAlgebra =
        targetEndSectorM2
    ; matrixSize =
        2
    ; matrixSizeMatchesTarget =
        refl
    ; laneDimensionMatchesMatrixSize =
        refl
    ; sectorAtom =
        DHR.SU2Sector
    ; sectorAtomMatchesFiniteRow =
        refl
    ; targetBoundary =
        "p3 targets EndSector(M2) by dimension-2 row evidence and the current SU2 sector atom"
        ∷ "The concrete M2 evidence is the canonical Clifford-even/M2 basis isomorphism"
        ∷ []
    }

p5M3EndSectorMatrixTargetRow :
  FinitePrimeLaneEndSectorMatrixTargetRow
p5M3EndSectorMatrixTargetRow =
  record
    { finiteRow =
        p5SU3cFinitePrimeLaneSMRow
    ; targetAlgebra =
        targetEndSectorM3
    ; matrixSize =
        3
    ; matrixSizeMatchesTarget =
        refl
    ; laneDimensionMatchesMatrixSize =
        refl
    ; sectorAtom =
        DHR.SU3Frontier
    ; sectorAtomMatchesFiniteRow =
        refl
    ; targetBoundary =
        "p5 targets EndSector(M3) by dimension-3 row evidence and the current SU3 frontier atom"
        ∷ "The concrete M3 evidence is the canonical W3-to-M3 clock-shift isomorphism"
        ∷ []
    }

canonicalFinitePrimeLaneEndSectorMatrixTargetRows :
  List FinitePrimeLaneEndSectorMatrixTargetRow
canonicalFinitePrimeLaneEndSectorMatrixTargetRows =
  p2CEndSectorMatrixTargetRow
  ∷ p3M2EndSectorMatrixTargetRow
  ∷ p5M3EndSectorMatrixTargetRow
  ∷ []

data FinitePrimeLaneEndSectorMatrixTargetBlocker : Set where
  missingDHRLocalisedEndomorphismAlgebraCarrier :
    FinitePrimeLaneEndSectorMatrixTargetBlocker

  missingEndSectorCompositionAndStarLaws :
    FinitePrimeLaneEndSectorMatrixTargetBlocker

  missingMatrixTargetToDHRSectorEquivalence :
    FinitePrimeLaneEndSectorMatrixTargetBlocker

  missingDRCompactGroupAndGSMComparison :
    FinitePrimeLaneEndSectorMatrixTargetBlocker

canonicalFinitePrimeLaneEndSectorMatrixTargetBlockers :
  List FinitePrimeLaneEndSectorMatrixTargetBlocker
canonicalFinitePrimeLaneEndSectorMatrixTargetBlockers =
  missingDHRLocalisedEndomorphismAlgebraCarrier
  ∷ missingEndSectorCompositionAndStarLaws
  ∷ missingMatrixTargetToDHRSectorEquivalence
  ∷ missingDRCompactGroupAndGSMComparison
  ∷ []

data P2ComplexScalarCarrier : Set where
  p2ScalarOne :
    P2ComplexScalarCarrier

p2ScalarMul :
  P2ComplexScalarCarrier →
  P2ComplexScalarCarrier →
  P2ComplexScalarCarrier
p2ScalarMul p2ScalarOne p2ScalarOne =
  p2ScalarOne

p2ScalarStar :
  P2ComplexScalarCarrier →
  P2ComplexScalarCarrier
p2ScalarStar p2ScalarOne =
  p2ScalarOne

p2ScalarLeftIdentity :
  (x : P2ComplexScalarCarrier) →
  p2ScalarMul p2ScalarOne x ≡ x
p2ScalarLeftIdentity p2ScalarOne =
  refl

p2ScalarRightIdentity :
  (x : P2ComplexScalarCarrier) →
  p2ScalarMul x p2ScalarOne ≡ x
p2ScalarRightIdentity p2ScalarOne =
  refl

p2ScalarStarInvolutive :
  (x : P2ComplexScalarCarrier) →
  p2ScalarStar (p2ScalarStar x) ≡ x
p2ScalarStarInvolutive p2ScalarOne =
  refl

record FinitePrimeLaneCarrierMatrixComputationReceipt : Setω where
  field
    p2ScalarCarrier :
      P2ComplexScalarCarrier

    p2ScalarCarrierIsCanonical :
      p2ScalarCarrier ≡ p2ScalarOne

    p2ScalarLeftIdentityLaw :
      p2ScalarMul p2ScalarOne p2ScalarCarrier
      ≡
      p2ScalarCarrier

    p2ScalarRightIdentityLaw :
      p2ScalarMul p2ScalarCarrier p2ScalarOne
      ≡
      p2ScalarCarrier

    p2ScalarStarLaw :
      p2ScalarStar (p2ScalarStar p2ScalarCarrier)
      ≡
      p2ScalarCarrier

    p3CliffordM2Iso :
      CliffordM2.CliffordM2BasisIso

    p3CliffordM2IsoIsCanonical :
      p3CliffordM2Iso ≡ CliffordM2.canonicalCliffordM2BasisIso

    p3M2RoundTripOnCanonicalBasis :
      (m : TMG.M2BasisElement) →
      CliffordM2.toM2 p3CliffordM2Iso
        (CliffordM2.fromM2 p3CliffordM2Iso m)
      ≡
      m

    p5W3ToM3Iso :
      W3Iso.W3ToM3Iso

    p5W3ToM3IsoIsCanonical :
      p5W3ToM3Iso ≡ W3Iso.canonicalW3ToM3Iso

    p5M3ClockShiftAlgebra :
      W3Iso.M3ClockShiftAlgebra

    p5M3ClockShiftAlgebraIsCanonical :
      p5M3ClockShiftAlgebra ≡ W3Iso.canonicalM3ClockShiftAlgebra

    p5ClockCubedIsIdentity :
      W3.matrixMul
        (W3.matrixMul
          (W3Iso.M3ClockShiftAlgebra.m3Clock p5M3ClockShiftAlgebra)
          (W3Iso.M3ClockShiftAlgebra.m3Clock p5M3ClockShiftAlgebra))
        (W3Iso.M3ClockShiftAlgebra.m3Clock p5M3ClockShiftAlgebra)
      ≡
      W3.identityMatrix3

    p5ShiftCubedIsIdentity :
      W3.matrixMul
        (W3.matrixMul
          (W3Iso.M3ClockShiftAlgebra.m3Shift p5M3ClockShiftAlgebra)
          (W3Iso.M3ClockShiftAlgebra.m3Shift p5M3ClockShiftAlgebra))
        (W3Iso.M3ClockShiftAlgebra.m3Shift p5M3ClockShiftAlgebra)
      ≡
      W3.identityMatrix3

    p5ClockShiftCommutation :
      W3.matrixMul
        (W3Iso.M3ClockShiftAlgebra.m3Shift p5M3ClockShiftAlgebra)
        (W3Iso.M3ClockShiftAlgebra.m3Clock p5M3ClockShiftAlgebra)
      ≡
      W3.scalarMul
        W3.omega
        (W3.matrixMul
          (W3Iso.M3ClockShiftAlgebra.m3Clock p5M3ClockShiftAlgebra)
          (W3Iso.M3ClockShiftAlgebra.m3Shift p5M3ClockShiftAlgebra))

    finiteCarrierMatrixComputationConstructed :
      Bool

    finiteCarrierMatrixComputationConstructedIsTrue :
      finiteCarrierMatrixComputationConstructed ≡ true

    dhrLocalisedEndomorphismAlgebraConstructed :
      Bool

    dhrLocalisedEndomorphismAlgebraConstructedIsFalse :
      dhrLocalisedEndomorphismAlgebraConstructed ≡ false

    computationBoundary :
      List String

open FinitePrimeLaneCarrierMatrixComputationReceipt public

canonicalFinitePrimeLaneCarrierMatrixComputationReceipt :
  FinitePrimeLaneCarrierMatrixComputationReceipt
canonicalFinitePrimeLaneCarrierMatrixComputationReceipt =
  record
    { p2ScalarCarrier =
        p2ScalarOne
    ; p2ScalarCarrierIsCanonical =
        refl
    ; p2ScalarLeftIdentityLaw =
        refl
    ; p2ScalarRightIdentityLaw =
        refl
    ; p2ScalarStarLaw =
        refl
    ; p3CliffordM2Iso =
        CliffordM2.canonicalCliffordM2BasisIso
    ; p3CliffordM2IsoIsCanonical =
        refl
    ; p3M2RoundTripOnCanonicalBasis =
        CliffordM2.toFrom CliffordM2.canonicalCliffordM2BasisIso
    ; p5W3ToM3Iso =
        W3Iso.canonicalW3ToM3Iso
    ; p5W3ToM3IsoIsCanonical =
        refl
    ; p5M3ClockShiftAlgebra =
        W3Iso.canonicalM3ClockShiftAlgebra
    ; p5M3ClockShiftAlgebraIsCanonical =
        refl
    ; p5ClockCubedIsIdentity =
        W3Iso.M3ClockShiftAlgebra.m3ClockCubedIsIdentity
          W3Iso.canonicalM3ClockShiftAlgebra
    ; p5ShiftCubedIsIdentity =
        W3Iso.M3ClockShiftAlgebra.m3ShiftCubedIsIdentity
          W3Iso.canonicalM3ClockShiftAlgebra
    ; p5ClockShiftCommutation =
        W3Iso.M3ClockShiftAlgebra.m3CommutationRelation
          W3Iso.canonicalM3ClockShiftAlgebra
    ; finiteCarrierMatrixComputationConstructed =
        true
    ; finiteCarrierMatrixComputationConstructedIsTrue =
        refl
    ; dhrLocalisedEndomorphismAlgebraConstructed =
        false
    ; dhrLocalisedEndomorphismAlgebraConstructedIsFalse =
        refl
    ; computationBoundary =
        "p2 has the finite one-dimensional scalar carrier with identity and involutive star laws"
        ∷ "p3 consumes the existing Clifford-even to M2 basis isomorphism and its round-trip law"
        ∷ "p5 consumes the existing W3-to-M3 clock-shift algebra with C^3=I, S^3=I, and SC=omega CS"
        ∷ "This computes finite carrier matrix targets only; it is not a DHR localised endomorphism category"
        ∷ []
    }

record FinitePrimeLaneEndSectorMatrixTargetReceipt : Setω where
  field
    ledgerRows :
      List FinitePrimeLaneSMRow

    ledgerRowsAreCanonical :
      ledgerRows ≡ canonicalFinitePrimeLaneSMRows

    endSectorTargetRows :
      List FinitePrimeLaneEndSectorMatrixTargetRow

    endSectorTargetRowsAreCanonical :
      endSectorTargetRows
      ≡
      canonicalFinitePrimeLaneEndSectorMatrixTargetRows

    p2TargetRow :
      FinitePrimeLaneEndSectorMatrixTargetRow

    p2TargetRowIsCanonical :
      p2TargetRow ≡ p2CEndSectorMatrixTargetRow

    p3TargetRow :
      FinitePrimeLaneEndSectorMatrixTargetRow

    p3TargetRowIsCanonical :
      p3TargetRow ≡ p3M2EndSectorMatrixTargetRow

    p5TargetRow :
      FinitePrimeLaneEndSectorMatrixTargetRow

    p5TargetRowIsCanonical :
      p5TargetRow ≡ p5M3EndSectorMatrixTargetRow

    u1SectorObject :
      DHR.U1SectorObject

    u1SectorObjectIsCanonical :
      u1SectorObject ≡ DHR.canonicalU1SectorObject

    su2SectorObject :
      DHR.SU2SectorObject

    su2SectorObjectIsCanonical :
      su2SectorObject ≡ DHR.canonicalSU2SectorObject

    su3FrontierObject :
      DHR.SU3FrontierObject

    su3FrontierObjectThreadedFromCanonical :
      Bool

    su3FrontierObjectThreadedFromCanonicalIsTrue :
      su3FrontierObjectThreadedFromCanonical ≡ true

    p3CliffordM2Iso :
      CliffordM2.CliffordM2BasisIso

    p3CliffordM2IsoIsCanonical :
      p3CliffordM2Iso ≡ CliffordM2.canonicalCliffordM2BasisIso

    p5W3ToM3Iso :
      W3Iso.W3ToM3Iso

    p5W3ToM3IsoIsCanonical :
      p5W3ToM3Iso ≡ W3Iso.canonicalW3ToM3Iso

    p5M3ClockShiftAlgebra :
      W3Iso.M3ClockShiftAlgebra

    p5M3ClockShiftAlgebraIsCanonical :
      p5M3ClockShiftAlgebra ≡ W3Iso.canonicalM3ClockShiftAlgebra

    carrierMatrixComputation :
      FinitePrimeLaneCarrierMatrixComputationReceipt

    carrierMatrixComputationThreadedFromCanonical :
      Bool

    carrierMatrixComputationThreadedFromCanonicalIsTrue :
      carrierMatrixComputationThreadedFromCanonical ≡ true

    blockers :
      List FinitePrimeLaneEndSectorMatrixTargetBlocker

    blockersAreCanonical :
      blockers ≡ canonicalFinitePrimeLaneEndSectorMatrixTargetBlockers

    firstBlocker :
      FinitePrimeLaneEndSectorMatrixTargetBlocker

    firstBlockerIsDHRLocalisedEndomorphismAlgebraCarrier :
      firstBlocker ≡ missingDHRLocalisedEndomorphismAlgebraCarrier

    cM2M3TargetsRecorded :
      Bool

    cM2M3TargetsRecordedIsTrue :
      cM2M3TargetsRecorded ≡ true

    finiteCarrierMatrixComputationConstructed :
      Bool

    finiteCarrierMatrixComputationConstructedIsTrue :
      finiteCarrierMatrixComputationConstructed ≡ true

    actualEndSectorAlgebraConstructed :
      Bool

    actualEndSectorAlgebraConstructedIsFalse :
      actualEndSectorAlgebraConstructed ≡ false

    drCompactGroupPromotion :
      Bool

    drCompactGroupPromotionIsFalse :
      drCompactGroupPromotion ≡ false

    gDHREqualsGSMPredictionPromoted :
      Bool

    gDHREqualsGSMPredictionPromotedIsFalse :
      gDHREqualsGSMPredictionPromoted ≡ false

    receiptBoundary :
      List String

open FinitePrimeLaneEndSectorMatrixTargetReceipt public

canonicalFinitePrimeLaneEndSectorMatrixTargetReceipt :
  FinitePrimeLaneEndSectorMatrixTargetReceipt
canonicalFinitePrimeLaneEndSectorMatrixTargetReceipt =
  record
    { ledgerRows =
        canonicalFinitePrimeLaneSMRows
    ; ledgerRowsAreCanonical =
        refl
    ; endSectorTargetRows =
        canonicalFinitePrimeLaneEndSectorMatrixTargetRows
    ; endSectorTargetRowsAreCanonical =
        refl
    ; p2TargetRow =
        p2CEndSectorMatrixTargetRow
    ; p2TargetRowIsCanonical =
        refl
    ; p3TargetRow =
        p3M2EndSectorMatrixTargetRow
    ; p3TargetRowIsCanonical =
        refl
    ; p5TargetRow =
        p5M3EndSectorMatrixTargetRow
    ; p5TargetRowIsCanonical =
        refl
    ; u1SectorObject =
        DHR.canonicalU1SectorObject
    ; u1SectorObjectIsCanonical =
        refl
    ; su2SectorObject =
        DHR.canonicalSU2SectorObject
    ; su2SectorObjectIsCanonical =
        refl
    ; su3FrontierObject =
        DHR.canonicalSU3FrontierObject
    ; su3FrontierObjectThreadedFromCanonical =
        true
    ; su3FrontierObjectThreadedFromCanonicalIsTrue =
        refl
    ; p3CliffordM2Iso =
        CliffordM2.canonicalCliffordM2BasisIso
    ; p3CliffordM2IsoIsCanonical =
        refl
    ; p5W3ToM3Iso =
        W3Iso.canonicalW3ToM3Iso
    ; p5W3ToM3IsoIsCanonical =
        refl
    ; p5M3ClockShiftAlgebra =
        W3Iso.canonicalM3ClockShiftAlgebra
    ; p5M3ClockShiftAlgebraIsCanonical =
        refl
    ; carrierMatrixComputation =
        canonicalFinitePrimeLaneCarrierMatrixComputationReceipt
    ; carrierMatrixComputationThreadedFromCanonical =
        true
    ; carrierMatrixComputationThreadedFromCanonicalIsTrue =
        refl
    ; blockers =
        canonicalFinitePrimeLaneEndSectorMatrixTargetBlockers
    ; blockersAreCanonical =
        refl
    ; firstBlocker =
        missingDHRLocalisedEndomorphismAlgebraCarrier
    ; firstBlockerIsDHRLocalisedEndomorphismAlgebraCarrier =
        refl
    ; cM2M3TargetsRecorded =
        true
    ; cM2M3TargetsRecordedIsTrue =
        refl
    ; finiteCarrierMatrixComputationConstructed =
        true
    ; finiteCarrierMatrixComputationConstructedIsTrue =
        refl
    ; actualEndSectorAlgebraConstructed =
        false
    ; actualEndSectorAlgebraConstructedIsFalse =
        refl
    ; drCompactGroupPromotion =
        false
    ; drCompactGroupPromotionIsFalse =
        refl
    ; gDHREqualsGSMPredictionPromoted =
        false
    ; gDHREqualsGSMPredictionPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Finite target rows package p2->C, p3->M2, and p5->M3 from the existing lane-dimension equalities"
        ∷ "p2 carries a finite one-dimensional scalar carrier; p3 carries the canonical Clifford-even/M2 basis isomorphism; p5 carries the canonical W3-to-M3 clock-shift isomorphism"
        ∷ "The finite carrier matrix computation is constructed for the p2/p3/p5 targets"
        ∷ "Actual EndSector algebra, target-to-DHR equivalence, DR compact-group reconstruction, and G_DHR ~= G_SM prediction promotion remain explicitly false"
        ∷ []
    }

data FinitePrimeLaneLocalisedEndomorphismKind : Set where
  p2CarrierLocalisedEndomorphism :
    FinitePrimeLaneLocalisedEndomorphismKind

  p3CarrierLocalisedEndomorphism :
    FinitePrimeLaneLocalisedEndomorphismKind

  p5CarrierLocalisedEndomorphism :
    FinitePrimeLaneLocalisedEndomorphismKind

finitePrimeLaneLocalisedEndomorphismRow :
  FinitePrimeLaneLocalisedEndomorphismKind →
  FinitePrimeLaneSMRow
finitePrimeLaneLocalisedEndomorphismRow p2CarrierLocalisedEndomorphism =
  p2U1YFinitePrimeLaneSMRow
finitePrimeLaneLocalisedEndomorphismRow p3CarrierLocalisedEndomorphism =
  p3SU2LFinitePrimeLaneSMRow
finitePrimeLaneLocalisedEndomorphismRow p5CarrierLocalisedEndomorphism =
  p5SU3cFinitePrimeLaneSMRow

finitePrimeLaneLocalisedEndomorphismMatrixTargetRow :
  FinitePrimeLaneLocalisedEndomorphismKind →
  FinitePrimeLaneEndSectorMatrixTargetRow
finitePrimeLaneLocalisedEndomorphismMatrixTargetRow
  p2CarrierLocalisedEndomorphism =
  p2CEndSectorMatrixTargetRow
finitePrimeLaneLocalisedEndomorphismMatrixTargetRow
  p3CarrierLocalisedEndomorphism =
  p3M2EndSectorMatrixTargetRow
finitePrimeLaneLocalisedEndomorphismMatrixTargetRow
  p5CarrierLocalisedEndomorphism =
  p5M3EndSectorMatrixTargetRow

finitePrimeLaneLocalisedEndomorphismCarrier :
  FinitePrimeLaneLocalisedEndomorphismKind →
  Set
finitePrimeLaneLocalisedEndomorphismCarrier
  p2CarrierLocalisedEndomorphism =
  P2ComplexScalarCarrier
finitePrimeLaneLocalisedEndomorphismCarrier
  p3CarrierLocalisedEndomorphism =
  TMG.M2BasisElement
finitePrimeLaneLocalisedEndomorphismCarrier
  p5CarrierLocalisedEndomorphism =
  W3Iso.M3Carrier

finitePrimeLaneLocalisedEndomorphismSelectedCarrier :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  finitePrimeLaneLocalisedEndomorphismCarrier kind
finitePrimeLaneLocalisedEndomorphismSelectedCarrier
  p2CarrierLocalisedEndomorphism =
  p2ScalarOne
finitePrimeLaneLocalisedEndomorphismSelectedCarrier
  p3CarrierLocalisedEndomorphism =
  TMG.e11
finitePrimeLaneLocalisedEndomorphismSelectedCarrier
  p5CarrierLocalisedEndomorphism =
  W3.identityMatrix3

finitePrimeLaneLocalisedEndomorphismAction :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  finitePrimeLaneLocalisedEndomorphismCarrier kind →
  finitePrimeLaneLocalisedEndomorphismCarrier kind
finitePrimeLaneLocalisedEndomorphismAction _ carrier =
  carrier

finitePrimeLaneLocalisedEndomorphismIdentityLaw :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
  finitePrimeLaneLocalisedEndomorphismAction kind carrier
  ≡
  carrier
finitePrimeLaneLocalisedEndomorphismIdentityLaw _ _ =
  refl

finitePrimeLaneLocalisedEndomorphismCompositionLaw :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
  finitePrimeLaneLocalisedEndomorphismAction kind
    (finitePrimeLaneLocalisedEndomorphismAction kind carrier)
  ≡
  finitePrimeLaneLocalisedEndomorphismAction kind carrier
finitePrimeLaneLocalisedEndomorphismCompositionLaw _ _ =
  refl

finitePrimeLaneLocalisedEndomorphismStarHom :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  finitePrimeLaneLocalisedEndomorphismCarrier kind →
  finitePrimeLaneLocalisedEndomorphismCarrier kind
finitePrimeLaneLocalisedEndomorphismStarHom _ carrier =
  carrier

finitePrimeLaneLocalisedEndomorphismStarInvolutive :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
  finitePrimeLaneLocalisedEndomorphismStarHom kind
    (finitePrimeLaneLocalisedEndomorphismStarHom kind carrier)
  ≡
  carrier
finitePrimeLaneLocalisedEndomorphismStarInvolutive _ _ =
  refl

finitePrimeLaneLocalisedEndomorphismComposedAction :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  finitePrimeLaneLocalisedEndomorphismCarrier kind →
  finitePrimeLaneLocalisedEndomorphismCarrier kind
finitePrimeLaneLocalisedEndomorphismComposedAction kind carrier =
  finitePrimeLaneLocalisedEndomorphismAction kind
    (finitePrimeLaneLocalisedEndomorphismAction kind carrier)

finitePrimeLaneLocalisedEndomorphismCompositionAssociative :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
  finitePrimeLaneLocalisedEndomorphismAction kind
    (finitePrimeLaneLocalisedEndomorphismComposedAction kind carrier)
  ≡
  finitePrimeLaneLocalisedEndomorphismComposedAction kind
    (finitePrimeLaneLocalisedEndomorphismAction kind carrier)
finitePrimeLaneLocalisedEndomorphismCompositionAssociative _ _ =
  refl

------------------------------------------------------------------------
-- Finite prime-lane pair-swap braiding naturality primitives.
--
-- This is a bounded p2/p3/p5 carrier-level braiding surface.  The braiding
-- map swaps the two selected finite carrier fibres, and the naturality square
-- is inhabited against the existing identity localised endomorphisms and
-- `FinitePrimeLaneDHRArrow` identity/composition ledger.  It is not a DR
-- braiding theorem and does not promote a Standard Model equivalence.

record FinitePrimeLaneCarrierPair
  (left right : FinitePrimeLaneLocalisedEndomorphismKind) :
  Set where
  constructor finitePrimeLaneCarrierPair
  field
    leftCarrier :
      finitePrimeLaneLocalisedEndomorphismCarrier left

    rightCarrier :
      finitePrimeLaneLocalisedEndomorphismCarrier right

open FinitePrimeLaneCarrierPair public

finitePrimeLaneCarrierPairAction :
  (left right : FinitePrimeLaneLocalisedEndomorphismKind) →
  FinitePrimeLaneCarrierPair left right →
  FinitePrimeLaneCarrierPair left right
finitePrimeLaneCarrierPairAction left right pair =
  finitePrimeLaneCarrierPair
    (finitePrimeLaneLocalisedEndomorphismAction left
      (FinitePrimeLaneCarrierPair.leftCarrier pair))
    (finitePrimeLaneLocalisedEndomorphismAction right
      (FinitePrimeLaneCarrierPair.rightCarrier pair))

finitePrimeLanePairSwap :
  (left right : FinitePrimeLaneLocalisedEndomorphismKind) →
  FinitePrimeLaneCarrierPair left right →
  FinitePrimeLaneCarrierPair right left
finitePrimeLanePairSwap left right pair =
  finitePrimeLaneCarrierPair
    (FinitePrimeLaneCarrierPair.rightCarrier pair)
    (FinitePrimeLaneCarrierPair.leftCarrier pair)

finitePrimeLanePairSwapNaturalitySquare :
  (left right : FinitePrimeLaneLocalisedEndomorphismKind) →
  (pair : FinitePrimeLaneCarrierPair left right) →
  finitePrimeLanePairSwap left right
    (finitePrimeLaneCarrierPairAction left right pair)
  ≡
  finitePrimeLaneCarrierPairAction right left
    (finitePrimeLanePairSwap left right pair)
finitePrimeLanePairSwapNaturalitySquare _ _ _ =
  refl

record FinitePrimeLaneDHRPairTensorArrow
  (left right : FinitePrimeLaneLocalisedEndomorphismKind) :
  Set where
  field
    leftArrow :
      FinitePrimeLaneDHRArrow
        (finitePrimeLaneLocalisedEndomorphismRow left)
        (finitePrimeLaneLocalisedEndomorphismRow left)

    leftArrowIsIdentity :
      leftArrow
      ≡
      finitePrimeLaneId (finitePrimeLaneLocalisedEndomorphismRow left)

    rightArrow :
      FinitePrimeLaneDHRArrow
        (finitePrimeLaneLocalisedEndomorphismRow right)
        (finitePrimeLaneLocalisedEndomorphismRow right)

    rightArrowIsIdentity :
      rightArrow
      ≡
      finitePrimeLaneId (finitePrimeLaneLocalisedEndomorphismRow right)

    tensorComposeLaw :
      finitePrimeLaneDHRCompose leftArrow leftArrow
      ≡
      leftArrow

    tensorRightComposeLaw :
      finitePrimeLaneDHRCompose rightArrow rightArrow
      ≡
      rightArrow

open FinitePrimeLaneDHRPairTensorArrow public

finitePrimeLaneDHRPairIdentityTensorArrow :
  (left right : FinitePrimeLaneLocalisedEndomorphismKind) →
  FinitePrimeLaneDHRPairTensorArrow left right
finitePrimeLaneDHRPairIdentityTensorArrow left right =
  record
    { leftArrow =
        finitePrimeLaneId (finitePrimeLaneLocalisedEndomorphismRow left)
    ; leftArrowIsIdentity =
        refl
    ; rightArrow =
        finitePrimeLaneId (finitePrimeLaneLocalisedEndomorphismRow right)
    ; rightArrowIsIdentity =
        refl
    ; tensorComposeLaw =
        refl
    ; tensorRightComposeLaw =
        refl
    }

record FinitePrimeLanePairSwapBraidingIntertwiner
  (left right : FinitePrimeLaneLocalisedEndomorphismKind) :
  Set₁ where
  field
    sourceLeftRow :
      FinitePrimeLaneSMRow

    sourceLeftRowIsCanonical :
      sourceLeftRow ≡ finitePrimeLaneLocalisedEndomorphismRow left

    sourceRightRow :
      FinitePrimeLaneSMRow

    sourceRightRowIsCanonical :
      sourceRightRow ≡ finitePrimeLaneLocalisedEndomorphismRow right

    swappedLeftRow :
      FinitePrimeLaneSMRow

    swappedLeftRowIsSourceRight :
      swappedLeftRow ≡ sourceRightRow

    swappedRightRow :
      FinitePrimeLaneSMRow

    swappedRightRowIsSourceLeft :
      swappedRightRow ≡ sourceLeftRow

    sourceTensorArrow :
      FinitePrimeLaneDHRPairTensorArrow left right

    sourceTensorArrowIsIdentity :
      sourceTensorArrow
      ≡
      finitePrimeLaneDHRPairIdentityTensorArrow left right

    swappedTensorArrow :
      FinitePrimeLaneDHRPairTensorArrow right left

    swappedTensorArrowIsIdentity :
      swappedTensorArrow
      ≡
      finitePrimeLaneDHRPairIdentityTensorArrow right left

    braidMap :
      FinitePrimeLaneCarrierPair left right →
      FinitePrimeLaneCarrierPair right left

    braidMapIsPairSwap :
      braidMap ≡ finitePrimeLanePairSwap left right

    naturalitySquare :
      (pair : FinitePrimeLaneCarrierPair left right) →
      braidMap (finitePrimeLaneCarrierPairAction left right pair)
      ≡
      finitePrimeLaneCarrierPairAction right left (braidMap pair)

    braidingNaturalityConstructed :
      Bool

    braidingNaturalityConstructedIsTrue :
      braidingNaturalityConstructed ≡ true

    arbitraryDHRBraidingPromoted :
      Bool

    arbitraryDHRBraidingPromotedIsFalse :
      arbitraryDHRBraidingPromoted ≡ false

    drSMBraidingPromoted :
      Bool

    drSMBraidingPromotedIsFalse :
      drSMBraidingPromoted ≡ false

    braidingBoundary :
      List String

open FinitePrimeLanePairSwapBraidingIntertwiner public

finitePrimeLanePairSwapBraidingIntertwiner :
  (left right : FinitePrimeLaneLocalisedEndomorphismKind) →
  FinitePrimeLanePairSwapBraidingIntertwiner left right
finitePrimeLanePairSwapBraidingIntertwiner left right =
  record
    { sourceLeftRow =
        finitePrimeLaneLocalisedEndomorphismRow left
    ; sourceLeftRowIsCanonical =
        refl
    ; sourceRightRow =
        finitePrimeLaneLocalisedEndomorphismRow right
    ; sourceRightRowIsCanonical =
        refl
    ; swappedLeftRow =
        finitePrimeLaneLocalisedEndomorphismRow right
    ; swappedLeftRowIsSourceRight =
        refl
    ; swappedRightRow =
        finitePrimeLaneLocalisedEndomorphismRow left
    ; swappedRightRowIsSourceLeft =
        refl
    ; sourceTensorArrow =
        finitePrimeLaneDHRPairIdentityTensorArrow left right
    ; sourceTensorArrowIsIdentity =
        refl
    ; swappedTensorArrow =
        finitePrimeLaneDHRPairIdentityTensorArrow right left
    ; swappedTensorArrowIsIdentity =
        refl
    ; braidMap =
        finitePrimeLanePairSwap left right
    ; braidMapIsPairSwap =
        refl
    ; naturalitySquare =
        finitePrimeLanePairSwapNaturalitySquare left right
    ; braidingNaturalityConstructed =
        true
    ; braidingNaturalityConstructedIsTrue =
        refl
    ; arbitraryDHRBraidingPromoted =
        false
    ; arbitraryDHRBraidingPromotedIsFalse =
        refl
    ; drSMBraidingPromoted =
        false
    ; drSMBraidingPromotedIsFalse =
        refl
    ; braidingBoundary =
        "Finite pair-swap braiding is implemented only for selected finite p2/p3/p5 carrier-level localised endomorphism rows"
        ∷ "The tensor arrows are existing FinitePrimeLaneDHRArrow identity arrows on each component, composed by finitePrimeLaneDHRCompose"
        ∷ "The naturality square is definitional because each selected localised endomorphism action is identity on its finite carrier"
        ∷ "No arbitrary DHR braiding, Doplicher-Roberts reconstruction, or Standard Model group equivalence is promoted"
        ∷ []
    }

p2p3FinitePrimeLanePairSwapBraidingIntertwiner :
  FinitePrimeLanePairSwapBraidingIntertwiner
    p2CarrierLocalisedEndomorphism
    p3CarrierLocalisedEndomorphism
p2p3FinitePrimeLanePairSwapBraidingIntertwiner =
  finitePrimeLanePairSwapBraidingIntertwiner
    p2CarrierLocalisedEndomorphism
    p3CarrierLocalisedEndomorphism

p2p5FinitePrimeLanePairSwapBraidingIntertwiner :
  FinitePrimeLanePairSwapBraidingIntertwiner
    p2CarrierLocalisedEndomorphism
    p5CarrierLocalisedEndomorphism
p2p5FinitePrimeLanePairSwapBraidingIntertwiner =
  finitePrimeLanePairSwapBraidingIntertwiner
    p2CarrierLocalisedEndomorphism
    p5CarrierLocalisedEndomorphism

p3p5FinitePrimeLanePairSwapBraidingIntertwiner :
  FinitePrimeLanePairSwapBraidingIntertwiner
    p3CarrierLocalisedEndomorphism
    p5CarrierLocalisedEndomorphism
p3p5FinitePrimeLanePairSwapBraidingIntertwiner =
  finitePrimeLanePairSwapBraidingIntertwiner
    p3CarrierLocalisedEndomorphism
    p5CarrierLocalisedEndomorphism

record FinitePrimeLanePairSwapBraidingNaturalityReceipt : Set₁ where
  field
    p2p3Braiding :
      FinitePrimeLanePairSwapBraidingIntertwiner
        p2CarrierLocalisedEndomorphism
        p3CarrierLocalisedEndomorphism

    p2p3BraidingIsCanonical :
      p2p3Braiding ≡ p2p3FinitePrimeLanePairSwapBraidingIntertwiner

    p2p5Braiding :
      FinitePrimeLanePairSwapBraidingIntertwiner
        p2CarrierLocalisedEndomorphism
        p5CarrierLocalisedEndomorphism

    p2p5BraidingIsCanonical :
      p2p5Braiding ≡ p2p5FinitePrimeLanePairSwapBraidingIntertwiner

    p3p5Braiding :
      FinitePrimeLanePairSwapBraidingIntertwiner
        p3CarrierLocalisedEndomorphism
        p5CarrierLocalisedEndomorphism

    p3p5BraidingIsCanonical :
      p3p5Braiding ≡ p3p5FinitePrimeLanePairSwapBraidingIntertwiner

    p2p3NaturalitySquare :
      (pair :
        FinitePrimeLaneCarrierPair
          p2CarrierLocalisedEndomorphism
          p3CarrierLocalisedEndomorphism) →
      FinitePrimeLanePairSwapBraidingIntertwiner.braidMap
        p2p3Braiding
        (finitePrimeLaneCarrierPairAction
          p2CarrierLocalisedEndomorphism
          p3CarrierLocalisedEndomorphism
          pair)
      ≡
      finitePrimeLaneCarrierPairAction
        p3CarrierLocalisedEndomorphism
        p2CarrierLocalisedEndomorphism
        (FinitePrimeLanePairSwapBraidingIntertwiner.braidMap
          p2p3Braiding
          pair)

    p2p5NaturalitySquare :
      (pair :
        FinitePrimeLaneCarrierPair
          p2CarrierLocalisedEndomorphism
          p5CarrierLocalisedEndomorphism) →
      FinitePrimeLanePairSwapBraidingIntertwiner.braidMap
        p2p5Braiding
        (finitePrimeLaneCarrierPairAction
          p2CarrierLocalisedEndomorphism
          p5CarrierLocalisedEndomorphism
          pair)
      ≡
      finitePrimeLaneCarrierPairAction
        p5CarrierLocalisedEndomorphism
        p2CarrierLocalisedEndomorphism
        (FinitePrimeLanePairSwapBraidingIntertwiner.braidMap
          p2p5Braiding
          pair)

    p3p5NaturalitySquare :
      (pair :
        FinitePrimeLaneCarrierPair
          p3CarrierLocalisedEndomorphism
          p5CarrierLocalisedEndomorphism) →
      FinitePrimeLanePairSwapBraidingIntertwiner.braidMap
        p3p5Braiding
        (finitePrimeLaneCarrierPairAction
          p3CarrierLocalisedEndomorphism
          p5CarrierLocalisedEndomorphism
          pair)
      ≡
      finitePrimeLaneCarrierPairAction
        p5CarrierLocalisedEndomorphism
        p3CarrierLocalisedEndomorphism
        (FinitePrimeLanePairSwapBraidingIntertwiner.braidMap
          p3p5Braiding
          pair)

    pairSwapBraidingNaturalityConstructed :
      Bool

    pairSwapBraidingNaturalityConstructedIsTrue :
      pairSwapBraidingNaturalityConstructed ≡ true

    drSMBraidingPromotion :
      Bool

    drSMBraidingPromotionIsFalse :
      drSMBraidingPromotion ≡ false

    receiptBoundary :
      List String

open FinitePrimeLanePairSwapBraidingNaturalityReceipt public

canonicalFinitePrimeLanePairSwapBraidingNaturalityReceipt :
  FinitePrimeLanePairSwapBraidingNaturalityReceipt
canonicalFinitePrimeLanePairSwapBraidingNaturalityReceipt =
  record
    { p2p3Braiding =
        p2p3FinitePrimeLanePairSwapBraidingIntertwiner
    ; p2p3BraidingIsCanonical =
        refl
    ; p2p5Braiding =
        p2p5FinitePrimeLanePairSwapBraidingIntertwiner
    ; p2p5BraidingIsCanonical =
        refl
    ; p3p5Braiding =
        p3p5FinitePrimeLanePairSwapBraidingIntertwiner
    ; p3p5BraidingIsCanonical =
        refl
    ; p2p3NaturalitySquare =
        FinitePrimeLanePairSwapBraidingIntertwiner.naturalitySquare
          p2p3FinitePrimeLanePairSwapBraidingIntertwiner
    ; p2p5NaturalitySquare =
        FinitePrimeLanePairSwapBraidingIntertwiner.naturalitySquare
          p2p5FinitePrimeLanePairSwapBraidingIntertwiner
    ; p3p5NaturalitySquare =
        FinitePrimeLanePairSwapBraidingIntertwiner.naturalitySquare
          p3p5FinitePrimeLanePairSwapBraidingIntertwiner
    ; pairSwapBraidingNaturalityConstructed =
        true
    ; pairSwapBraidingNaturalityConstructedIsTrue =
        refl
    ; drSMBraidingPromotion =
        false
    ; drSMBraidingPromotionIsFalse =
        refl
    ; receiptBoundary =
        "The finite pair-swap naturality receipt covers p2/p3, p2/p5, and p3/p5 carrier pairs"
        ∷ "Each square uses identity FinitePrimeLaneDHRArrow tensor components and the concrete carrier pair swap"
        ∷ "Each naturality law reduces by refl because the localised endomorphism actions are identity maps on the finite carriers"
        ∷ "DR braiding and Standard Model equivalence promotion remain false"
        ∷ []
    }

record FinitePrimeLaneCarrierLevelLocalisedEndomorphism
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) :
  Set₁ where
  field
    finiteRow :
      FinitePrimeLaneSMRow

    finiteRowIsCanonical :
      finiteRow ≡ finitePrimeLaneLocalisedEndomorphismRow kind

    matrixTargetRow :
      FinitePrimeLaneEndSectorMatrixTargetRow

    matrixTargetRowIsCanonical :
      matrixTargetRow
      ≡
      finitePrimeLaneLocalisedEndomorphismMatrixTargetRow kind

    targetAlgebra :
      EndSectorMatrixTarget

    targetAlgebraMatchesMatrixRow :
      targetAlgebra
      ≡
      FinitePrimeLaneEndSectorMatrixTargetRow.targetAlgebra matrixTargetRow

    carrier :
      Set

    carrierIsCanonical :
      carrier
      ≡
      finitePrimeLaneLocalisedEndomorphismCarrier kind

    selectedCarrier :
      finitePrimeLaneLocalisedEndomorphismCarrier kind

    selectedCarrierIsCanonical :
      selectedCarrier
      ≡
      finitePrimeLaneLocalisedEndomorphismSelectedCarrier kind

    localisedEndomorphismAction :
      finitePrimeLaneLocalisedEndomorphismCarrier kind →
      finitePrimeLaneLocalisedEndomorphismCarrier kind

    localisedEndomorphismActionIsCanonical :
      localisedEndomorphismAction
      ≡
      finitePrimeLaneLocalisedEndomorphismAction kind

    localisedEndomorphismIdentityLaw :
      (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
      localisedEndomorphismAction carrier ≡ carrier

    localisedEndomorphismCompositionLaw :
      (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
      localisedEndomorphismAction
        (localisedEndomorphismAction carrier)
      ≡
      localisedEndomorphismAction carrier

    localisedEndomorphismStarHom :
      finitePrimeLaneLocalisedEndomorphismCarrier kind →
      finitePrimeLaneLocalisedEndomorphismCarrier kind

    localisedEndomorphismStarHomIsCanonical :
      localisedEndomorphismStarHom
      ≡
      finitePrimeLaneLocalisedEndomorphismStarHom kind

    localisedEndomorphismStarInvolutive :
      (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
      localisedEndomorphismStarHom
        (localisedEndomorphismStarHom carrier)
      ≡
      carrier

    localisedEndomorphismComposedAction :
      finitePrimeLaneLocalisedEndomorphismCarrier kind →
      finitePrimeLaneLocalisedEndomorphismCarrier kind

    localisedEndomorphismComposedActionIsCanonical :
      localisedEndomorphismComposedAction
      ≡
      finitePrimeLaneLocalisedEndomorphismComposedAction kind

    localisedEndomorphismAssociativityLaw :
      (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
      localisedEndomorphismAction
        (localisedEndomorphismComposedAction carrier)
      ≡
      localisedEndomorphismComposedAction
        (localisedEndomorphismAction carrier)

    finiteEndAlgebraReceiptsConstructed :
      Bool

    finiteEndAlgebraReceiptsConstructedIsTrue :
      finiteEndAlgebraReceiptsConstructed ≡ true

    selectedCarrierFixed :
      localisedEndomorphismAction selectedCarrier
      ≡
      selectedCarrier

    sectorAtom :
      DHR.DHRGaugeSectorAtom

    sectorAtomMatchesFiniteRow :
      sectorAtom ≡ FinitePrimeLaneSMRow.sectorAtom finiteRow

    carrierLevelLocalisedEndomorphismConstructed :
      Bool

    carrierLevelLocalisedEndomorphismConstructedIsTrue :
      carrierLevelLocalisedEndomorphismConstructed ≡ true

    carrierLevelBoundary :
      List String

open FinitePrimeLaneCarrierLevelLocalisedEndomorphism public

finitePrimeLaneCarrierLevelLocalisedEndomorphism :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  FinitePrimeLaneCarrierLevelLocalisedEndomorphism kind
finitePrimeLaneCarrierLevelLocalisedEndomorphism
  p2CarrierLocalisedEndomorphism =
  record
    { finiteRow =
        p2U1YFinitePrimeLaneSMRow
    ; finiteRowIsCanonical =
        refl
    ; matrixTargetRow =
        p2CEndSectorMatrixTargetRow
    ; matrixTargetRowIsCanonical =
        refl
    ; targetAlgebra =
        targetEndSectorC
    ; targetAlgebraMatchesMatrixRow =
        refl
    ; carrier =
        P2ComplexScalarCarrier
    ; carrierIsCanonical =
        refl
    ; selectedCarrier =
        p2ScalarOne
    ; selectedCarrierIsCanonical =
        refl
    ; localisedEndomorphismAction =
        finitePrimeLaneLocalisedEndomorphismAction
          p2CarrierLocalisedEndomorphism
    ; localisedEndomorphismActionIsCanonical =
        refl
    ; localisedEndomorphismIdentityLaw =
        finitePrimeLaneLocalisedEndomorphismIdentityLaw
          p2CarrierLocalisedEndomorphism
    ; localisedEndomorphismCompositionLaw =
        finitePrimeLaneLocalisedEndomorphismCompositionLaw
          p2CarrierLocalisedEndomorphism
    ; localisedEndomorphismStarHom =
        finitePrimeLaneLocalisedEndomorphismStarHom
          p2CarrierLocalisedEndomorphism
    ; localisedEndomorphismStarHomIsCanonical =
        refl
    ; localisedEndomorphismStarInvolutive =
        finitePrimeLaneLocalisedEndomorphismStarInvolutive
          p2CarrierLocalisedEndomorphism
    ; localisedEndomorphismComposedAction =
        finitePrimeLaneLocalisedEndomorphismComposedAction
          p2CarrierLocalisedEndomorphism
    ; localisedEndomorphismComposedActionIsCanonical =
        refl
    ; localisedEndomorphismAssociativityLaw =
        finitePrimeLaneLocalisedEndomorphismCompositionAssociative
          p2CarrierLocalisedEndomorphism
    ; finiteEndAlgebraReceiptsConstructed =
        true
    ; finiteEndAlgebraReceiptsConstructedIsTrue =
        refl
    ; selectedCarrierFixed =
        refl
    ; sectorAtom =
        DHR.U1Sector
    ; sectorAtomMatchesFiniteRow =
        refl
    ; carrierLevelLocalisedEndomorphismConstructed =
        true
    ; carrierLevelLocalisedEndomorphismConstructedIsTrue =
        refl
    ; carrierLevelBoundary =
        "p2 carrier-level localised endomorphism is the identity action on the inhabited one-point scalar carrier"
        ∷ "The finite p2 row records EndSector(C), identity composition, associativity, and star-hom involution receipts"
        ∷ "The action is tied to the p2->EndSector(C) matrix target row and the U1 sector atom"
        ∷ []
    }
finitePrimeLaneCarrierLevelLocalisedEndomorphism
  p3CarrierLocalisedEndomorphism =
  record
    { finiteRow =
        p3SU2LFinitePrimeLaneSMRow
    ; finiteRowIsCanonical =
        refl
    ; matrixTargetRow =
        p3M2EndSectorMatrixTargetRow
    ; matrixTargetRowIsCanonical =
        refl
    ; targetAlgebra =
        targetEndSectorM2
    ; targetAlgebraMatchesMatrixRow =
        refl
    ; carrier =
        TMG.M2BasisElement
    ; carrierIsCanonical =
        refl
    ; selectedCarrier =
        TMG.e11
    ; selectedCarrierIsCanonical =
        refl
    ; localisedEndomorphismAction =
        finitePrimeLaneLocalisedEndomorphismAction
          p3CarrierLocalisedEndomorphism
    ; localisedEndomorphismActionIsCanonical =
        refl
    ; localisedEndomorphismIdentityLaw =
        finitePrimeLaneLocalisedEndomorphismIdentityLaw
          p3CarrierLocalisedEndomorphism
    ; localisedEndomorphismCompositionLaw =
        finitePrimeLaneLocalisedEndomorphismCompositionLaw
          p3CarrierLocalisedEndomorphism
    ; localisedEndomorphismStarHom =
        finitePrimeLaneLocalisedEndomorphismStarHom
          p3CarrierLocalisedEndomorphism
    ; localisedEndomorphismStarHomIsCanonical =
        refl
    ; localisedEndomorphismStarInvolutive =
        finitePrimeLaneLocalisedEndomorphismStarInvolutive
          p3CarrierLocalisedEndomorphism
    ; localisedEndomorphismComposedAction =
        finitePrimeLaneLocalisedEndomorphismComposedAction
          p3CarrierLocalisedEndomorphism
    ; localisedEndomorphismComposedActionIsCanonical =
        refl
    ; localisedEndomorphismAssociativityLaw =
        finitePrimeLaneLocalisedEndomorphismCompositionAssociative
          p3CarrierLocalisedEndomorphism
    ; finiteEndAlgebraReceiptsConstructed =
        true
    ; finiteEndAlgebraReceiptsConstructedIsTrue =
        refl
    ; selectedCarrierFixed =
        refl
    ; sectorAtom =
        DHR.SU2Sector
    ; sectorAtomMatchesFiniteRow =
        refl
    ; carrierLevelLocalisedEndomorphismConstructed =
        true
    ; carrierLevelLocalisedEndomorphismConstructedIsTrue =
        refl
    ; carrierLevelBoundary =
        "p3 carrier-level localised endomorphism is the identity action on the inhabited M2 basis carrier"
        ∷ "The finite p3 row records EndSector(M2), identity composition, associativity, and star-hom involution receipts"
        ∷ "The action is tied to the p3->EndSector(M2) matrix target row and the SU2 sector atom"
        ∷ "The p3 M2 carrier is the same finite basis used by the canonical Clifford-even/M2 isomorphism"
        ∷ []
    }
finitePrimeLaneCarrierLevelLocalisedEndomorphism
  p5CarrierLocalisedEndomorphism =
  record
    { finiteRow =
        p5SU3cFinitePrimeLaneSMRow
    ; finiteRowIsCanonical =
        refl
    ; matrixTargetRow =
        p5M3EndSectorMatrixTargetRow
    ; matrixTargetRowIsCanonical =
        refl
    ; targetAlgebra =
        targetEndSectorM3
    ; targetAlgebraMatchesMatrixRow =
        refl
    ; carrier =
        W3Iso.M3Carrier
    ; carrierIsCanonical =
        refl
    ; selectedCarrier =
        W3.identityMatrix3
    ; selectedCarrierIsCanonical =
        refl
    ; localisedEndomorphismAction =
        finitePrimeLaneLocalisedEndomorphismAction
          p5CarrierLocalisedEndomorphism
    ; localisedEndomorphismActionIsCanonical =
        refl
    ; localisedEndomorphismIdentityLaw =
        finitePrimeLaneLocalisedEndomorphismIdentityLaw
          p5CarrierLocalisedEndomorphism
    ; localisedEndomorphismCompositionLaw =
        finitePrimeLaneLocalisedEndomorphismCompositionLaw
          p5CarrierLocalisedEndomorphism
    ; localisedEndomorphismStarHom =
        finitePrimeLaneLocalisedEndomorphismStarHom
          p5CarrierLocalisedEndomorphism
    ; localisedEndomorphismStarHomIsCanonical =
        refl
    ; localisedEndomorphismStarInvolutive =
        finitePrimeLaneLocalisedEndomorphismStarInvolutive
          p5CarrierLocalisedEndomorphism
    ; localisedEndomorphismComposedAction =
        finitePrimeLaneLocalisedEndomorphismComposedAction
          p5CarrierLocalisedEndomorphism
    ; localisedEndomorphismComposedActionIsCanonical =
        refl
    ; localisedEndomorphismAssociativityLaw =
        finitePrimeLaneLocalisedEndomorphismCompositionAssociative
          p5CarrierLocalisedEndomorphism
    ; finiteEndAlgebraReceiptsConstructed =
        true
    ; finiteEndAlgebraReceiptsConstructedIsTrue =
        refl
    ; selectedCarrierFixed =
        refl
    ; sectorAtom =
        DHR.SU3Frontier
    ; sectorAtomMatchesFiniteRow =
        refl
    ; carrierLevelLocalisedEndomorphismConstructed =
        true
    ; carrierLevelLocalisedEndomorphismConstructedIsTrue =
        refl
    ; carrierLevelBoundary =
        "p5 carrier-level localised endomorphism is the identity action on the inhabited M3 clock-shift carrier"
        ∷ "The finite p5 row records EndSector(M3), identity composition, associativity, and star-hom involution receipts"
        ∷ "The action is tied to the p5->EndSector(M3) matrix target row and the SU3 frontier atom"
        ∷ "The p5 M3 carrier is the same concrete carrier used by the canonical W3-to-M3 clock-shift isomorphism"
        ∷ []
    }

p2FinitePrimeLaneCarrierLevelLocalisedEndomorphism :
  FinitePrimeLaneCarrierLevelLocalisedEndomorphism
    p2CarrierLocalisedEndomorphism
p2FinitePrimeLaneCarrierLevelLocalisedEndomorphism =
  finitePrimeLaneCarrierLevelLocalisedEndomorphism
    p2CarrierLocalisedEndomorphism

p3FinitePrimeLaneCarrierLevelLocalisedEndomorphism :
  FinitePrimeLaneCarrierLevelLocalisedEndomorphism
    p3CarrierLocalisedEndomorphism
p3FinitePrimeLaneCarrierLevelLocalisedEndomorphism =
  finitePrimeLaneCarrierLevelLocalisedEndomorphism
    p3CarrierLocalisedEndomorphism

p5FinitePrimeLaneCarrierLevelLocalisedEndomorphism :
  FinitePrimeLaneCarrierLevelLocalisedEndomorphism
    p5CarrierLocalisedEndomorphism
p5FinitePrimeLaneCarrierLevelLocalisedEndomorphism =
  finitePrimeLaneCarrierLevelLocalisedEndomorphism
    p5CarrierLocalisedEndomorphism

record FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) :
  Set₁ where
  field
    localisedEndomorphism :
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism kind

    endAlgebra :
      EndSectorMatrixTarget

    endAlgebraMatchesMatrixTarget :
      endAlgebra
      ≡
      FinitePrimeLaneEndSectorMatrixTargetRow.targetAlgebra
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.matrixTargetRow
          localisedEndomorphism)

    starHom :
      finitePrimeLaneLocalisedEndomorphismCarrier kind →
      finitePrimeLaneLocalisedEndomorphismCarrier kind

    starHomIsCanonical :
      starHom
      ≡
      finitePrimeLaneLocalisedEndomorphismStarHom kind

    starHomInvolutive :
      (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
      starHom (starHom carrier) ≡ carrier

    composedAction :
      finitePrimeLaneLocalisedEndomorphismCarrier kind →
      finitePrimeLaneLocalisedEndomorphismCarrier kind

    composedActionIsCanonical :
      composedAction
      ≡
      finitePrimeLaneLocalisedEndomorphismComposedAction kind

    compositionAssociative :
      (carrier : finitePrimeLaneLocalisedEndomorphismCarrier kind) →
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
        localisedEndomorphism
        (composedAction carrier)
      ≡
      composedAction
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
          localisedEndomorphism
          carrier)

    starAlgebraPackConstructed :
      Bool

    starAlgebraPackConstructedIsTrue :
      starAlgebraPackConstructed ≡ true

    packBoundary :
      List String

open FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack public

finitePrimeLaneLocalisedEndomorphismStarAlgebraPack :
  (kind : FinitePrimeLaneLocalisedEndomorphismKind) →
  FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack kind
finitePrimeLaneLocalisedEndomorphismStarAlgebraPack
  p2CarrierLocalisedEndomorphism =
  record
    { localisedEndomorphism =
        finitePrimeLaneCarrierLevelLocalisedEndomorphism
          p2CarrierLocalisedEndomorphism
    ; endAlgebra =
        targetEndSectorC
    ; endAlgebraMatchesMatrixTarget =
        refl
    ; starHom =
        finitePrimeLaneLocalisedEndomorphismStarHom
          p2CarrierLocalisedEndomorphism
    ; starHomIsCanonical =
        refl
    ; starHomInvolutive =
        finitePrimeLaneLocalisedEndomorphismStarInvolutive
          p2CarrierLocalisedEndomorphism
    ; composedAction =
        finitePrimeLaneLocalisedEndomorphismComposedAction
          p2CarrierLocalisedEndomorphism
    ; composedActionIsCanonical =
        refl
    ; compositionAssociative =
        finitePrimeLaneLocalisedEndomorphismCompositionAssociative
          p2CarrierLocalisedEndomorphism
    ; starAlgebraPackConstructed =
        true
    ; starAlgebraPackConstructedIsTrue =
        refl
    ; packBoundary =
        "p2 finite localised endomorphism star/algebra pack uses EndSector(C) and identity star"
        ∷ "Composition is associative definitionally because the finite p2 action is the identity action"
        ∷ []
    }
finitePrimeLaneLocalisedEndomorphismStarAlgebraPack
  p3CarrierLocalisedEndomorphism =
  record
    { localisedEndomorphism =
        finitePrimeLaneCarrierLevelLocalisedEndomorphism
          p3CarrierLocalisedEndomorphism
    ; endAlgebra =
        targetEndSectorM2
    ; endAlgebraMatchesMatrixTarget =
        refl
    ; starHom =
        finitePrimeLaneLocalisedEndomorphismStarHom
          p3CarrierLocalisedEndomorphism
    ; starHomIsCanonical =
        refl
    ; starHomInvolutive =
        finitePrimeLaneLocalisedEndomorphismStarInvolutive
          p3CarrierLocalisedEndomorphism
    ; composedAction =
        finitePrimeLaneLocalisedEndomorphismComposedAction
          p3CarrierLocalisedEndomorphism
    ; composedActionIsCanonical =
        refl
    ; compositionAssociative =
        finitePrimeLaneLocalisedEndomorphismCompositionAssociative
          p3CarrierLocalisedEndomorphism
    ; starAlgebraPackConstructed =
        true
    ; starAlgebraPackConstructedIsTrue =
        refl
    ; packBoundary =
        "p3 finite localised endomorphism star/algebra pack uses EndSector(M2) and identity star over the Clifford/M2 carrier"
        ∷ "Composition is associative definitionally because the finite p3 action is the identity action"
        ∷ []
    }
finitePrimeLaneLocalisedEndomorphismStarAlgebraPack
  p5CarrierLocalisedEndomorphism =
  record
    { localisedEndomorphism =
        finitePrimeLaneCarrierLevelLocalisedEndomorphism
          p5CarrierLocalisedEndomorphism
    ; endAlgebra =
        targetEndSectorM3
    ; endAlgebraMatchesMatrixTarget =
        refl
    ; starHom =
        finitePrimeLaneLocalisedEndomorphismStarHom
          p5CarrierLocalisedEndomorphism
    ; starHomIsCanonical =
        refl
    ; starHomInvolutive =
        finitePrimeLaneLocalisedEndomorphismStarInvolutive
          p5CarrierLocalisedEndomorphism
    ; composedAction =
        finitePrimeLaneLocalisedEndomorphismComposedAction
          p5CarrierLocalisedEndomorphism
    ; composedActionIsCanonical =
        refl
    ; compositionAssociative =
        finitePrimeLaneLocalisedEndomorphismCompositionAssociative
          p5CarrierLocalisedEndomorphism
    ; starAlgebraPackConstructed =
        true
    ; starAlgebraPackConstructedIsTrue =
        refl
    ; packBoundary =
        "p5 finite localised endomorphism star/algebra pack uses EndSector(M3) and identity star over the W3/M3 carrier"
        ∷ "Composition is associative definitionally because the finite p5 action is the identity action"
        ∷ []
    }

p2FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack :
  FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack
    p2CarrierLocalisedEndomorphism
p2FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack =
  finitePrimeLaneLocalisedEndomorphismStarAlgebraPack
    p2CarrierLocalisedEndomorphism

p3FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack :
  FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack
    p3CarrierLocalisedEndomorphism
p3FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack =
  finitePrimeLaneLocalisedEndomorphismStarAlgebraPack
    p3CarrierLocalisedEndomorphism

p5FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack :
  FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack
    p5CarrierLocalisedEndomorphism
p5FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack =
  finitePrimeLaneLocalisedEndomorphismStarAlgebraPack
    p5CarrierLocalisedEndomorphism

record FinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt : Setω where
  field
    matrixTargetReceipt :
      FinitePrimeLaneEndSectorMatrixTargetReceipt

    carrierMatrixComputation :
      FinitePrimeLaneCarrierMatrixComputationReceipt

    p2LocalisedEndomorphism :
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism
        p2CarrierLocalisedEndomorphism

    p3LocalisedEndomorphism :
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism
        p3CarrierLocalisedEndomorphism

    p5LocalisedEndomorphism :
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism
        p5CarrierLocalisedEndomorphism

    p2ActionFixesScalarOne :
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
        p2LocalisedEndomorphism
        p2ScalarOne
      ≡
      p2ScalarOne

    p3ActionFixesM2Basis :
      (basis : TMG.M2BasisElement) →
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
        p3LocalisedEndomorphism
        basis
      ≡
      basis

    p5ActionFixesClockMatrix :
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
        p5LocalisedEndomorphism
        W3.clockMatrix
      ≡
      W3.clockMatrix

    p5ActionFixesShiftMatrix :
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
        p5LocalisedEndomorphism
        W3.shiftMatrix
      ≡
      W3.shiftMatrix

    p5ClockShiftComputationRetained :
      W3.matrixMul W3.shiftMatrix W3.clockMatrix
      ≡
      W3.scalarMul
        W3.omega
        (W3.matrixMul W3.clockMatrix W3.shiftMatrix)

    p2StarHomInvolutive :
      (carrier : P2ComplexScalarCarrier) →
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismStarHom
        p2LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismStarHom
          p2LocalisedEndomorphism
          carrier)
      ≡
      carrier

    p3StarHomInvolutive :
      (carrier : TMG.M2BasisElement) →
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismStarHom
        p3LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismStarHom
          p3LocalisedEndomorphism
          carrier)
      ≡
      carrier

    p5StarHomInvolutive :
      (carrier : W3Iso.M3Carrier) →
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismStarHom
        p5LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismStarHom
          p5LocalisedEndomorphism
          carrier)
      ≡
      carrier

    p2EndCompositionAssociative :
      (carrier : P2ComplexScalarCarrier) →
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
        p2LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismComposedAction
          p2LocalisedEndomorphism
          carrier)
      ≡
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismComposedAction
        p2LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
          p2LocalisedEndomorphism
          carrier)

    p3EndCompositionAssociative :
      (carrier : TMG.M2BasisElement) →
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
        p3LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismComposedAction
          p3LocalisedEndomorphism
          carrier)
      ≡
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismComposedAction
        p3LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
          p3LocalisedEndomorphism
          carrier)

    p5EndCompositionAssociative :
      (carrier : W3Iso.M3Carrier) →
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
        p5LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismComposedAction
          p5LocalisedEndomorphism
          carrier)
      ≡
      FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismComposedAction
        p5LocalisedEndomorphism
        (FinitePrimeLaneCarrierLevelLocalisedEndomorphism.localisedEndomorphismAction
          p5LocalisedEndomorphism
          carrier)

    carrierLevelLocalisedEndomorphismLaneConstructed :
      Bool

    carrierLevelLocalisedEndomorphismLaneConstructedIsTrue :
      carrierLevelLocalisedEndomorphismLaneConstructed ≡ true

    receiptBoundary :
      List String

open FinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt public

canonicalFinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt :
  FinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt
canonicalFinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt =
  record
    { matrixTargetReceipt =
        canonicalFinitePrimeLaneEndSectorMatrixTargetReceipt
    ; carrierMatrixComputation =
        canonicalFinitePrimeLaneCarrierMatrixComputationReceipt
    ; p2LocalisedEndomorphism =
        finitePrimeLaneCarrierLevelLocalisedEndomorphism
          p2CarrierLocalisedEndomorphism
    ; p3LocalisedEndomorphism =
        finitePrimeLaneCarrierLevelLocalisedEndomorphism
          p3CarrierLocalisedEndomorphism
    ; p5LocalisedEndomorphism =
        finitePrimeLaneCarrierLevelLocalisedEndomorphism
          p5CarrierLocalisedEndomorphism
    ; p2ActionFixesScalarOne =
        refl
    ; p3ActionFixesM2Basis =
        λ _ →
          refl
    ; p5ActionFixesClockMatrix =
        refl
    ; p5ActionFixesShiftMatrix =
        refl
    ; p5ClockShiftComputationRetained =
        W3.commutationRelation
    ; p2StarHomInvolutive =
        λ _ →
          refl
    ; p3StarHomInvolutive =
        λ _ →
          refl
    ; p5StarHomInvolutive =
        λ _ →
          refl
    ; p2EndCompositionAssociative =
        λ _ →
          refl
    ; p3EndCompositionAssociative =
        λ _ →
          refl
    ; p5EndCompositionAssociative =
        λ _ →
          refl
    ; carrierLevelLocalisedEndomorphismLaneConstructed =
        true
    ; carrierLevelLocalisedEndomorphismLaneConstructedIsTrue =
        refl
    ; receiptBoundary =
        "Carrier-level localised endomorphism lane is inhabited for the already-computed p2, p3, and p5 matrix targets"
        ∷ "Each finite lane uses the identity endomorphism on its concrete carrier: p2 scalar, p3 M2 basis, and p5 M3 clock-shift matrices"
        ∷ "Each row carries explicit finite EndSector target, star-hom involution, composition, and associativity receipts"
        ∷ "The p5 clock-shift computation is retained through the same concrete W3-to-M3 carrier"
        ∷ "This is a finite carrier-level lane package, not an arbitrary DHR category, DR compact-group reconstruction, or Standard Model equivalence"
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

    pairSwapBraidingNaturality :
      FinitePrimeLanePairSwapBraidingNaturalityReceipt

    endRhoPkRepGPkBlocker :
      PrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt

    endSectorMatrixTargetReceipt :
      FinitePrimeLaneEndSectorMatrixTargetReceipt

    carrierLevelLocalisedEndomorphismReceipt :
      FinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt

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
    ; pairSwapBraidingNaturality =
        canonicalFinitePrimeLanePairSwapBraidingNaturalityReceipt
    ; endRhoPkRepGPkBlocker =
        canonicalPrimeLaneEndRhoPkRepGPkExactMatchBlockerReceipt
    ; endSectorMatrixTargetReceipt =
        canonicalFinitePrimeLaneEndSectorMatrixTargetReceipt
    ; carrierLevelLocalisedEndomorphismReceipt =
        canonicalFinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt
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
        ∷ "The EndSector matrix target receipt packages p2->C, p3->M2, and p5->M3 without constructing the actual EndSector algebra"
        ∷ "The carrier-level localised endomorphism receipt inhabits identity endomorphism actions on the p2, p3, and p5 matrix carriers"
        ∷ "Finite identity, identity-composition, row-naturality, and pair-swap braiding naturality receipts are inhabited"
        ∷ "Exact End(rho_pk) ~= Rep(G_pk), Gate1/Gate6 exact match, and G_DHR ~= G_SM remain explicitly false promotions"
        ∷ []
    }
