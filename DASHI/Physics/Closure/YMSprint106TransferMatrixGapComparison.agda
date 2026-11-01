module DASHI.Physics.Closure.YMSprint106TransferMatrixGapComparison where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.CarrierOS3ReflectionPositivityReceipt as OS3
import DASHI.Physics.Closure.LatticeMassGapFromTransferMatrixReceipt as LatticeGap
import DASHI.Physics.Closure.YMSprint105NonCircularMassGapBridge as Sprint105

------------------------------------------------------------------------
-- Sprint 106 transfer-matrix comparison side.
--
-- This is a DASHI-native status receipt, not a Clay proof.  It records the
-- finite transfer-matrix facts already available in the imported receipts and
-- keeps the uniform continuum lower bound and comparison theorem as open
-- obligations.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

transferMatrixComparisonReceiptRecorded : Bool
transferMatrixComparisonReceiptRecorded = true

finiteTransferMatrixDefined : Bool
finiteTransferMatrixDefined =
  LatticeGap.transferMatrixDefined
    LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt

finiteTransferGapPositive : Bool
finiteTransferGapPositive =
  LatticeGap.finiteLatticeGapPositive
    LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt

uniformContinuumLowerBoundProved : Bool
uniformContinuumLowerBoundProved = false

comparisonTargetLocallyProved : Bool
comparisonTargetLocallyProved = false

dashiNativeComparisonTargetRequired : Bool
dashiNativeComparisonTargetRequired = true

transferMatrixDefinitionStatement : String
transferMatrixDefinitionStatement =
  "The finite-lattice transfer matrix is defined by the imported LatticeMassGapFromTransferMatrixReceipt."

finiteGapStatement : String
finiteGapStatement =
  "The finite-lattice transfer gap is positive at the receipt scope supported by reflection positivity and discrete finite-lattice spectrum."

uniformContinuumLowerBoundStatement : String
uniformContinuumLowerBoundStatement =
  "A uniform lower bound that survives the continuum limit is still required and is not proved in this module."

comparisonTargetFormula : String
comparisonTargetFormula =
  "gap(T(a)) >= c * m_eff(a) * a"

comparisonTargetStatement : String
comparisonTargetStatement =
  "The comparison target gap(T(a)) >= c * m_eff(a) * a remains the DASHI-native theorem obligation unless separately proved."

nonPromotionBoundaryStatement : String
nonPromotionBoundaryStatement =
  "This receipt records finite transfer-matrix support and an open DASHI-native comparison obligation; it does not promote the Clay Yang-Mills mass gap."

record TransferMatrixDefinedStatus : Set where
  constructor mkTransferMatrixDefinedStatus
  field
    source :
      String
    statement :
      String
    importedReceiptSaysDefined :
      Bool
    os3ReceiptSaysDefined :
      Bool
    transferMatrixDefined :
      Bool
    finiteScopeOnly :
      Bool

record FiniteLatticeGapPositiveStatus : Set where
  constructor mkFiniteLatticeGapPositiveStatus
  field
    source :
      String
    statement :
      String
    importedReceiptSaysPositive :
      Bool
    os3ReceiptSaysPositive :
      Bool
    finiteLatticeGapPositive :
      Bool
    continuumGapNotInferred :
      Bool

record UniformContinuumLowerBoundStatus : Set where
  constructor mkUniformContinuumLowerBoundStatus
  field
    statement :
      String
    required :
      Bool
    provedHere :
      Bool
    inheritedFromTransferReceipt :
      Bool
    inheritedFromSprint105Bridge :
      Bool

record ComparisonTargetStatus : Set where
  constructor mkComparisonTargetStatus
  field
    formula :
      String
    statement :
      String
    dashiNativeTheoremObligation :
      Bool
    locallyProved :
      Bool
    clayClaim :
      Bool

record NonPromotionBoundary : Set where
  constructor mkNonPromotionBoundary
  field
    statement :
      String
    clayYangMillsPromotedHere :
      Bool
    sprint105ClayPromoted :
      Bool
    transferReceiptClayPromoted :
      Bool
    os3ReceiptClayPromoted :
      Bool

record Sprint106DependencyLedger : Set where
  constructor mkSprint106DependencyLedger
  field
    transferMassGapReceipt :
      String
    transferMatrixDefinedFromTransferReceipt :
      Bool
    finiteGapPositiveFromTransferReceipt :
      Bool
    carrierOS3ReflectionPositivityReceipt :
      String
    transferMatrixDefinedFromOS3Receipt :
      Bool
    finiteGapPositiveFromOS3Receipt :
      Bool
    sprint105NonCircularMassGapBridge :
      String
    sprint105ComparisonTargetFormula :
      String
    sprint105ComparisonTargetStillOpen :
      Bool

record YMSprint106TransferMatrixGapComparisonReceipt : Set where
  field
    transferMatrixStatus :
      TransferMatrixDefinedStatus
    finiteGapStatus :
      FiniteLatticeGapPositiveStatus
    uniformContinuumLowerBoundStatus :
      UniformContinuumLowerBoundStatus
    comparisonTargetStatus :
      ComparisonTargetStatus
    dependencyLedger :
      Sprint106DependencyLedger
    nonPromotionBoundary :
      NonPromotionBoundary
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool

canonicalTransferMatrixDefinedStatus :
  TransferMatrixDefinedStatus
canonicalTransferMatrixDefinedStatus =
  mkTransferMatrixDefinedStatus
    "LatticeMassGapFromTransferMatrixReceipt and CarrierOS3ReflectionPositivityReceipt"
    transferMatrixDefinitionStatement
    finiteTransferMatrixDefined
    true
    true
    true

canonicalFiniteLatticeGapPositiveStatus :
  FiniteLatticeGapPositiveStatus
canonicalFiniteLatticeGapPositiveStatus =
  mkFiniteLatticeGapPositiveStatus
    "LatticeMassGapFromTransferMatrixReceipt"
    finiteGapStatement
    finiteTransferGapPositive
    true
    true
    true

canonicalUniformContinuumLowerBoundStatus :
  UniformContinuumLowerBoundStatus
canonicalUniformContinuumLowerBoundStatus =
  mkUniformContinuumLowerBoundStatus
    uniformContinuumLowerBoundStatement
    true
    uniformContinuumLowerBoundProved
    (LatticeGap.uniformContinuumGapProved
      LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt)
    Sprint105.dashiNativeGapTransferTheoremProved

canonicalComparisonTargetStatus :
  ComparisonTargetStatus
canonicalComparisonTargetStatus =
  mkComparisonTargetStatus
    comparisonTargetFormula
    comparisonTargetStatement
    dashiNativeComparisonTargetRequired
    comparisonTargetLocallyProved
    false

canonicalNonPromotionBoundary :
  NonPromotionBoundary
canonicalNonPromotionBoundary =
  mkNonPromotionBoundary
    nonPromotionBoundaryStatement
    clayYangMillsPromoted
    Sprint105.clayYangMillsPromoted
    (LatticeGap.clayYangMillsPromoted
      LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt)
    (OS3.clayYangMillsPromoted
      OS3.canonicalCarrierOS3ReflectionPositivityReceipt)

canonicalSprint106DependencyLedger :
  Sprint106DependencyLedger
canonicalSprint106DependencyLedger =
  mkSprint106DependencyLedger
    "DASHI.Physics.Closure.LatticeMassGapFromTransferMatrixReceipt"
    (LatticeGap.transferMatrixDefined
      LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt)
    (LatticeGap.finiteLatticeGapPositive
      LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt)
    "DASHI.Physics.Closure.CarrierOS3ReflectionPositivityReceipt"
    true
    true
    "DASHI.Physics.Closure.YMSprint105NonCircularMassGapBridge"
    Sprint105.gapTransferObligationFormula
    Sprint105.dashiNativeGapTransferTheoremProved

canonicalYMSprint106TransferMatrixGapComparisonReceipt :
  YMSprint106TransferMatrixGapComparisonReceipt
canonicalYMSprint106TransferMatrixGapComparisonReceipt =
  record
    { transferMatrixStatus =
        canonicalTransferMatrixDefinedStatus
    ; finiteGapStatus =
        canonicalFiniteLatticeGapPositiveStatus
    ; uniformContinuumLowerBoundStatus =
        canonicalUniformContinuumLowerBoundStatus
    ; comparisonTargetStatus =
        canonicalComparisonTargetStatus
    ; dependencyLedger =
        canonicalSprint106DependencyLedger
    ; nonPromotionBoundary =
        canonicalNonPromotionBoundary
    ; receiptRecorded =
        transferMatrixComparisonReceiptRecorded
    ; clayYangMillsPromotedHere =
        clayYangMillsPromoted
    }

canonicalReceiptClayYangMillsPromoted :
  Bool
canonicalReceiptClayYangMillsPromoted =
  YMSprint106TransferMatrixGapComparisonReceipt.clayYangMillsPromotedHere
    canonicalYMSprint106TransferMatrixGapComparisonReceipt

canonicalReceiptComparisonTargetStillRequired :
  Bool
canonicalReceiptComparisonTargetStillRequired =
  ComparisonTargetStatus.dashiNativeTheoremObligation
    (YMSprint106TransferMatrixGapComparisonReceipt.comparisonTargetStatus
      canonicalYMSprint106TransferMatrixGapComparisonReceipt)

canonicalReceiptUniformContinuumLowerBoundStillOpen :
  Bool
canonicalReceiptUniformContinuumLowerBoundStillOpen =
  UniformContinuumLowerBoundStatus.provedHere
    (YMSprint106TransferMatrixGapComparisonReceipt.uniformContinuumLowerBoundStatus
      canonicalYMSprint106TransferMatrixGapComparisonReceipt)
