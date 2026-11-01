module DASHI.Physics.Closure.CKMPredictionFrontierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierDerived as CKMD
import DASHI.Physics.Closure.CKMCarrierMixingReceipt as Mix
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.CKMUnitarityFromCarrier as CKMU
import DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt as Ratios
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.YukawaFromCarrier as Yukawa
import DASHI.Physics.YM.WolfensteinCKM as Wolf

------------------------------------------------------------------------
-- CKM first-principles prediction frontier.
--
-- This receipt packages the current exact carrier, symbolic Wolfenstein/
-- Jarlskog target surface, and Yukawa prerequisites into one fail-closed
-- prediction frontier.  It records Vus/Vcb/Vub/delta/Jarlskog only as
-- observables with comparison-target labels.  No physical numeric value is
-- claimed as derived by this module.

data CKMPredictionObservable : Set where
  predictVus :
    CKMPredictionObservable

  predictVcb :
    CKMPredictionObservable

  predictVub :
    CKMPredictionObservable

  predictCPDelta :
    CKMPredictionObservable

  predictJarlskog :
    CKMPredictionObservable

canonicalCKMPredictionObservables :
  List CKMPredictionObservable
canonicalCKMPredictionObservables =
  predictVus
  ∷ predictVcb
  ∷ predictVub
  ∷ predictCPDelta
  ∷ predictJarlskog
  ∷ []

data CKMPredictionBlocker : Set where
  missingSymbolicFNChargeToPhysicalYukawaLaw :
    CKMPredictionBlocker

  missingApproximationErrorBoundForWolfensteinTruncation :
    CKMPredictionBlocker

  missingExactNonDiagonalYukawaEigenbasis :
    CKMPredictionBlocker

  missingExactCKMProductForPhysicalDiagonalizers :
    CKMPredictionBlocker

  missingDeltaAndJarlskogNonzeroDerivation :
    CKMPredictionBlocker

  missingMeasuredComparisonAsAuthorityOnly :
    CKMPredictionBlocker

canonicalCKMPredictionBlockers :
  List CKMPredictionBlocker
canonicalCKMPredictionBlockers =
  missingSymbolicFNChargeToPhysicalYukawaLaw
  ∷ missingApproximationErrorBoundForWolfensteinTruncation
  ∷ missingExactNonDiagonalYukawaEigenbasis
  ∷ missingExactCKMProductForPhysicalDiagonalizers
  ∷ missingDeltaAndJarlskogNonzeroDerivation
  ∷ missingMeasuredComparisonAsAuthorityOnly
  ∷ []

record CKMComparisonTarget : Set where
  constructor ckmComparisonTarget
  field
    observable :
      CKMPredictionObservable

    authorityLabel :
      String

    recordedAsComparisonOnly :
      Bool

    recordedAsComparisonOnlyIsTrue :
      recordedAsComparisonOnly ≡ true

    derivedByCarrier :
      Bool

    derivedByCarrierIsFalse :
      derivedByCarrier ≡ false

open CKMComparisonTarget public

pdg2025VusComparisonTarget : CKMComparisonTarget
pdg2025VusComparisonTarget =
  ckmComparisonTarget
    predictVus
    "PDG-2025 CKM |Vus| comparison target"
    true
    refl
    false
    refl

pdg2025VcbComparisonTarget : CKMComparisonTarget
pdg2025VcbComparisonTarget =
  ckmComparisonTarget
    predictVcb
    "PDG-2025 CKM |Vcb| comparison target"
    true
    refl
    false
    refl

pdg2025VubComparisonTarget : CKMComparisonTarget
pdg2025VubComparisonTarget =
  ckmComparisonTarget
    predictVub
    "PDG-2025 CKM |Vub| comparison target"
    true
    refl
    false
    refl

pdg2025DeltaComparisonTarget : CKMComparisonTarget
pdg2025DeltaComparisonTarget =
  ckmComparisonTarget
    predictCPDelta
    "PDG-2025 CKM CP phase delta comparison target"
    true
    refl
    false
    refl

pdg2025JarlskogComparisonTarget : CKMComparisonTarget
pdg2025JarlskogComparisonTarget =
  ckmComparisonTarget
    predictJarlskog
    "PDG-2025 CKM Jarlskog invariant comparison target"
    true
    refl
    false
    refl

canonicalCKMComparisonTargets :
  List CKMComparisonTarget
canonicalCKMComparisonTargets =
  pdg2025VusComparisonTarget
  ∷ pdg2025VcbComparisonTarget
  ∷ pdg2025VubComparisonTarget
  ∷ pdg2025DeltaComparisonTarget
  ∷ pdg2025JarlskogComparisonTarget
  ∷ []

record CKMPredictionFrontierReceipt : Setω where
  field
    carrierDerivedReceipt :
      CKMD.CKMCarrierDerivedReceipt

    carrierUnitarityReceipt :
      CKMU.CKMUnitaryReceipt

    carrierYukawaPrereqReceipt :
      Yukawa.YukawaFromCarrierReceipt

    carrierYukawaRatioTargetReceipt :
      Ratios.CarrierYukawaRatioTargetReceipt

    carrierYukawaRatioTargetReceiptThreaded :
      Bool

    carrierYukawaRatioTargetReceiptThreadedIsTrue :
      carrierYukawaRatioTargetReceiptThreaded ≡ true

    carrierYukawaRatioTargetsAreCanonical :
      Ratios.ratioTargets carrierYukawaRatioTargetReceipt
      ≡
      Ratios.canonicalCarrierYukawaRatioTargets

    carrierYukawaRatioBlockersAreCanonical :
      Ratios.ratioBlockers carrierYukawaRatioTargetReceipt
      ≡
      Ratios.canonicalCarrierYukawaRatioBlockers

    physicalYukawaRatioPredictionsPromoted :
      Bool

    physicalYukawaRatioPredictionsPromotedMatchesRatioReceipt :
      physicalYukawaRatioPredictionsPromoted
      ≡
      Ratios.physicalRatioPredictionsPromoted
        carrierYukawaRatioTargetReceipt

    physicalYukawaRatioPredictionsPromotedIsFalse :
      physicalYukawaRatioPredictionsPromoted ≡ false

    physicalFermionMassReceiptsForRatiosConstructed :
      Bool

    physicalFermionMassReceiptsForRatiosConstructedMatchesRatioReceipt :
      physicalFermionMassReceiptsForRatiosConstructed
      ≡
      Ratios.physicalFermionMassReceiptsConstructed
        carrierYukawaRatioTargetReceipt

    physicalFermionMassReceiptsForRatiosConstructedIsFalse :
      physicalFermionMassReceiptsForRatiosConstructed ≡ false

    physicalCarrierMixingBridge :
      Mix.PhysicalCarrierMixingBridge

    wolfensteinWitness :
      Wolf.WolfensteinCKMWitness

    wolfensteinJarlskogTargetSurface :
      Mix.CKMWolfensteinJarlskogTargetSurface

    exactWitnessChain :
      Exact.CKMExactWitnessChain

    carrierMatrix :
      Matter.MixingMatrix

    carrierMatrixIsExactIdentity :
      carrierMatrix ≡ Matter.identityMixingMatrix

    carrierMatrixAgreesWithDerivedReceipt :
      carrierMatrix
      ≡
      CKMD.ckmCarrierMatrix carrierDerivedReceipt

    carrierMatrixAgreesWithYukawaPrereq :
      carrierMatrix
      ≡
      Yukawa.ckmCarrierMatrix carrierYukawaPrereqReceipt

    upYukawaPrereq :
      Exact.DiagonalYukawa3x3

    upYukawaPrereqIsCarrierYukawa :
      upYukawaPrereq
      ≡
      Yukawa.upYukawa carrierYukawaPrereqReceipt

    upWeakBasisEigenbasisTransport :
      Yukawa.UpWeakBasisEigenbasisTransport

    upWeakBasisEigenbasisTransportIsCarrierYukawa :
      upWeakBasisEigenbasisTransport
      ≡
      Yukawa.upWeakBasisEigenbasisTransport
        carrierYukawaPrereqReceipt

    U_u :
      Matter.MixingMatrix

    U_uAgreesWithYukawaPrereq :
      U_u
      ≡
      Yukawa.U_u carrierYukawaPrereqReceipt

    U_uIsIdentity :
      U_u ≡ Matter.identityMixingMatrix

    U_uUnitaryClosure :
      Matter.leftIdentityMixingProduct U_u ≡ U_u

    U_uDiagonalisesCarrierUpYukawaYukawaDagger :
      Yukawa.UpWeakBasisEigenbasisTransport.transportedUpHermitianProduct
        upWeakBasisEigenbasisTransport
      ≡
      Yukawa.UpWeakBasisEigenbasisTransport.upHermitianProductMatrix
        upWeakBasisEigenbasisTransport

    downYukawaPrereq :
      Exact.DiagonalYukawa3x3

    downYukawaPrereqIsCarrierYukawa :
      downYukawaPrereq
      ≡
      Yukawa.downYukawa carrierYukawaPrereqReceipt

    downWeakBasisEigenbasisTransport :
      CKMD.DownWeakBasisEigenbasisTransport

    downTransportUd :
      Matter.MixingMatrix

    downTransportUdIsIdentity :
      downTransportUd ≡ Matter.identityMixingMatrix

    downTransportUdAgreesWithReceipt :
      downTransportUd
      ≡
      CKMD.U_d downWeakBasisEigenbasisTransport

    weakBasisProductClosureReceipt :
      CKMD.CKMWeakBasisProductClosureReceipt

    weakBasisProductMatrix :
      Matter.MixingMatrix

    weakBasisProductMatrixAgreesWithCarrier :
      weakBasisProductMatrix ≡ carrierMatrix

    weakBasisProductMatrixAgreesWithClosureReceipt :
      weakBasisProductMatrix
      ≡
      CKMD.productMatrix weakBasisProductClosureReceipt

    exactCarrierCKMProductClosureDerived :
      Bool

    exactCarrierCKMProductClosureDerivedIsTrue :
      exactCarrierCKMProductClosureDerived ≡ true

    predictionObservables :
      List CKMPredictionObservable

    predictionObservablesAreCanonical :
      predictionObservables
      ≡
      canonicalCKMPredictionObservables

    comparisonTargets :
      List CKMComparisonTarget

    comparisonTargetsAreCanonical :
      comparisonTargets
      ≡
      canonicalCKMComparisonTargets

    blockers :
      List CKMPredictionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMPredictionBlockers

    firstSymbolicBlocker :
      CKMPredictionBlocker

    firstSymbolicBlockerIsFNChargeLaw :
      firstSymbolicBlocker
      ≡
      missingSymbolicFNChargeToPhysicalYukawaLaw

    symbolicPredictionLawDerived :
      Bool

    symbolicPredictionLawDerivedIsFalse :
      symbolicPredictionLawDerived ≡ false

    approximationErrorBoundDerived :
      Bool

    approximationErrorBoundDerivedIsFalse :
      approximationErrorBoundDerived ≡ false

    exactPhysicalCKMProductDerived :
      Bool

    exactPhysicalCKMProductDerivedIsFalse :
      exactPhysicalCKMProductDerived ≡ false

    deltaAndJarlskogDerived :
      Bool

    deltaAndJarlskogDerivedIsFalse :
      deltaAndJarlskogDerived ≡ false

    comparisonTargetsPromotedToDerivations :
      Bool

    comparisonTargetsPromotedToDerivationsIsFalse :
      comparisonTargetsPromotedToDerivations ≡ false

    predictionFrontierPromoted :
      Bool

    predictionFrontierPromotedIsFalse :
      predictionFrontierPromoted ≡ false

    frontierBoundary :
      List String

open CKMPredictionFrontierReceipt public

canonicalCKMPredictionFrontierReceipt :
  CKMPredictionFrontierReceipt
canonicalCKMPredictionFrontierReceipt =
  record
    { carrierDerivedReceipt =
        CKMD.canonicalCKMCarrierDerived
    ; carrierUnitarityReceipt =
        CKMU.canonicalCKMUnitary
    ; carrierYukawaPrereqReceipt =
        Yukawa.canonicalYukawaFromCarrier
    ; carrierYukawaRatioTargetReceipt =
        Ratios.canonicalCarrierYukawaRatioTargetReceipt
    ; carrierYukawaRatioTargetReceiptThreaded =
        true
    ; carrierYukawaRatioTargetReceiptThreadedIsTrue =
        refl
    ; carrierYukawaRatioTargetsAreCanonical =
        Ratios.ratioTargetsAreCanonical
          Ratios.canonicalCarrierYukawaRatioTargetReceipt
    ; carrierYukawaRatioBlockersAreCanonical =
        Ratios.ratioBlockersAreCanonical
          Ratios.canonicalCarrierYukawaRatioTargetReceipt
    ; physicalYukawaRatioPredictionsPromoted =
        Ratios.physicalRatioPredictionsPromoted
          Ratios.canonicalCarrierYukawaRatioTargetReceipt
    ; physicalYukawaRatioPredictionsPromotedMatchesRatioReceipt =
        refl
    ; physicalYukawaRatioPredictionsPromotedIsFalse =
        Ratios.canonicalCarrierYukawaRatioTargetsKeepPhysicalPromotionClosed
    ; physicalFermionMassReceiptsForRatiosConstructed =
        Ratios.physicalFermionMassReceiptsConstructed
          Ratios.canonicalCarrierYukawaRatioTargetReceipt
    ; physicalFermionMassReceiptsForRatiosConstructedMatchesRatioReceipt =
        refl
    ; physicalFermionMassReceiptsForRatiosConstructedIsFalse =
        Ratios.canonicalCarrierYukawaRatioTargetsThreadDHRMassBlocker
    ; physicalCarrierMixingBridge =
        Mix.canonicalPhysicalCarrierMixingBridge
    ; wolfensteinWitness =
        Wolf.canonicalWolfensteinCKMWitness
    ; wolfensteinJarlskogTargetSurface =
        Mix.canonicalCKMWolfensteinJarlskogTargetSurface
    ; exactWitnessChain =
        Exact.canonicalCKMExactWitnessChain
    ; carrierMatrix =
        CKMD.ckmCarrierMatrix CKMD.canonicalCKMCarrierDerived
    ; carrierMatrixIsExactIdentity =
        refl
    ; carrierMatrixAgreesWithDerivedReceipt =
        refl
    ; carrierMatrixAgreesWithYukawaPrereq =
        refl
    ; upYukawaPrereq =
        Yukawa.upYukawa Yukawa.canonicalYukawaFromCarrier
    ; upYukawaPrereqIsCarrierYukawa =
        refl
    ; upWeakBasisEigenbasisTransport =
        Yukawa.upWeakBasisEigenbasisTransport
          Yukawa.canonicalYukawaFromCarrier
    ; upWeakBasisEigenbasisTransportIsCarrierYukawa =
        refl
    ; U_u =
        Yukawa.U_u Yukawa.canonicalYukawaFromCarrier
    ; U_uAgreesWithYukawaPrereq =
        refl
    ; U_uIsIdentity =
        refl
    ; U_uUnitaryClosure =
        refl
    ; U_uDiagonalisesCarrierUpYukawaYukawaDagger =
        Yukawa.U_uDiagonalisesCarrierUpYukawaYukawaDagger
          Yukawa.canonicalYukawaFromCarrier
    ; downYukawaPrereq =
        Yukawa.downYukawa Yukawa.canonicalYukawaFromCarrier
    ; downYukawaPrereqIsCarrierYukawa =
        refl
    ; downWeakBasisEigenbasisTransport =
        CKMD.downWeakBasisEigenbasisTransport
          CKMD.canonicalCKMCarrierDerived
    ; downTransportUd =
        CKMD.U_d
          (CKMD.downWeakBasisEigenbasisTransport
            CKMD.canonicalCKMCarrierDerived)
    ; downTransportUdIsIdentity =
        refl
    ; downTransportUdAgreesWithReceipt =
        refl
    ; weakBasisProductClosureReceipt =
        CKMD.weakBasisProductClosureReceipt
          CKMD.canonicalCKMCarrierDerived
    ; weakBasisProductMatrix =
        CKMD.productMatrix
          (CKMD.weakBasisProductClosureReceipt
            CKMD.canonicalCKMCarrierDerived)
    ; weakBasisProductMatrixAgreesWithCarrier =
        refl
    ; weakBasisProductMatrixAgreesWithClosureReceipt =
        refl
    ; exactCarrierCKMProductClosureDerived =
        true
    ; exactCarrierCKMProductClosureDerivedIsTrue =
        refl
    ; predictionObservables =
        canonicalCKMPredictionObservables
    ; predictionObservablesAreCanonical =
        refl
    ; comparisonTargets =
        canonicalCKMComparisonTargets
    ; comparisonTargetsAreCanonical =
        refl
    ; blockers =
        canonicalCKMPredictionBlockers
    ; blockersAreCanonical =
        refl
    ; firstSymbolicBlocker =
        missingSymbolicFNChargeToPhysicalYukawaLaw
    ; firstSymbolicBlockerIsFNChargeLaw =
        refl
    ; symbolicPredictionLawDerived =
        false
    ; symbolicPredictionLawDerivedIsFalse =
        refl
    ; approximationErrorBoundDerived =
        false
    ; approximationErrorBoundDerivedIsFalse =
        refl
    ; exactPhysicalCKMProductDerived =
        false
    ; exactPhysicalCKMProductDerivedIsFalse =
        refl
    ; deltaAndJarlskogDerived =
        false
    ; deltaAndJarlskogDerivedIsFalse =
        refl
    ; comparisonTargetsPromotedToDerivations =
        false
    ; comparisonTargetsPromotedToDerivationsIsFalse =
        refl
    ; predictionFrontierPromoted =
        false
    ; predictionFrontierPromotedIsFalse =
        refl
    ; frontierBoundary =
        "Vus, Vcb, Vub, delta, and Jarlskog are recorded as prediction observables"
        ∷ "PDG-2025 labels are comparison targets only, not derived values"
        ∷ "The exact carrier CKM remains the identity matrix and is linked to CKMCarrierDerived, CKMUnitarityFromCarrier, and YukawaFromCarrier"
        ∷ "The Yukawa prerequisites are the carrier up/down diagonal 3x3 witnesses from YukawaFromCarrier"
        ∷ "The carrier-Yukawa ratio target receipt is threaded as target bookkeeping; physical ratio predictions and physical fermion-mass receipts remain closed"
        ∷ "The down-sector weak-basis transport U_d is explicitly consumed from CKMCarrierDerived and is the identity diagonalizer"
        ∷ "The exact carrier CKM product closure U_u^dagger * U_d is consumed as a concrete identity-matrix receipt"
        ∷ "The Wolfenstein/Jarlskog surface is consumed as a symbolic target surface without numeric promotion"
        ∷ "Symbolic FN-charge-to-physical-Yukawa law, approximation error bounds, exact non-diagonal eigenbases, exact physical CKM product beyond the carrier identity case, and delta/Jarlskog nonzero derivation remain blockers"
        ∷ []
    }

ckmPredictionFrontierKeepsComparisonTargetsNonDerived :
  comparisonTargetsPromotedToDerivations
    canonicalCKMPredictionFrontierReceipt
  ≡
  false
ckmPredictionFrontierKeepsComparisonTargetsNonDerived =
  refl

ckmPredictionFrontierKeepsPhysicalPredictionClosed :
  predictionFrontierPromoted canonicalCKMPredictionFrontierReceipt
  ≡
  false
ckmPredictionFrontierKeepsPhysicalPredictionClosed =
  refl

ckmPredictionFrontierThreadsYukawaRatioTarget :
  carrierYukawaRatioTargetReceiptThreaded
    canonicalCKMPredictionFrontierReceipt
  ≡
  true
ckmPredictionFrontierThreadsYukawaRatioTarget =
  refl

ckmPredictionFrontierKeepsPhysicalYukawaRatioPredictionsClosed :
  physicalYukawaRatioPredictionsPromoted
    canonicalCKMPredictionFrontierReceipt
  ≡
  false
ckmPredictionFrontierKeepsPhysicalYukawaRatioPredictionsClosed =
  Ratios.canonicalCarrierYukawaRatioTargetsKeepPhysicalPromotionClosed

ckmPredictionFrontierKeepsPhysicalYukawaMassReceiptsClosed :
  physicalFermionMassReceiptsForRatiosConstructed
    canonicalCKMPredictionFrontierReceipt
  ≡
  false
ckmPredictionFrontierKeepsPhysicalYukawaMassReceiptsClosed =
  Ratios.canonicalCarrierYukawaRatioTargetsThreadDHRMassBlocker

ckmPredictionFrontierLinksCarrierYukawaPrereq :
  carrierMatrix canonicalCKMPredictionFrontierReceipt
  ≡
  Yukawa.ckmCarrierMatrix
    (carrierYukawaPrereqReceipt canonicalCKMPredictionFrontierReceipt)
ckmPredictionFrontierLinksCarrierYukawaPrereq =
  refl

ckmPredictionFrontierConsumesDownTransportUd :
  downTransportUd canonicalCKMPredictionFrontierReceipt
  ≡
  Matter.identityMixingMatrix
ckmPredictionFrontierConsumesDownTransportUd =
  refl

ckmPredictionFrontierConsumesCarrierProductClosure :
  exactCarrierCKMProductClosureDerived
    canonicalCKMPredictionFrontierReceipt
  ≡
  true
ckmPredictionFrontierConsumesCarrierProductClosure =
  refl
