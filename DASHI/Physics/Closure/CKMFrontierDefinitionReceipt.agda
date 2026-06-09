module DASHI.Physics.Closure.CKMFrontierDefinitionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM frontier definition receipt.
--
-- This receipt defines the three gates that must close before G7 can
-- unblock.  It records the current CKM frontier fail-closed: lambda is the
-- only proved CKM quantity, Vub remains a leading-order candidate, and Vcb
-- plus the unitarity-triangle angles remain ungrounded.

data CKMFrontierStatus : Set where
  blocked :
    CKMFrontierStatus

data CKMQuantity : Set where
  lambda :
    CKMQuantity

  Vcb :
    CKMQuantity

  Vub :
    CKMQuantity

  gamma :
    CKMQuantity

  beta :
    CKMQuantity

  alpha :
    CKMQuantity

data CKMCandidateHypothesis : Set where
  Vub_leading_order :
    CKMCandidateHypothesis

data CKMGate : Set where
  GateA :
    CKMGate

  GateB :
    CKMGate

  GateC :
    CKMGate

data CKMGateState : Set where
  openUntilTheorem :
    CKMGateState

  openUntilIndependentDerivation :
    CKMGateState

  openUntilFullMatrixPhaseDerivation :
    CKMGateState

data CKMGateObligation : Set where
  DMinusSevenSelectionTheorem :
    CKMGateObligation

  IndependentVcbWithoutPDGAInput :
    CKMGateObligation

  FullVubBeyondDownIdentity :
    CKMGateObligation

data CKMQuantityStatus : Set where
  proved :
    CKMQuantityStatus

  pdgTautology :
    CKMQuantityStatus

  leadingOrderEstimate :
    CKMQuantityStatus

  ungrounded :
    CKMQuantityStatus

canonicalCKMProvedQuantities :
  List CKMQuantity
canonicalCKMProvedQuantities =
  lambda
  ∷ []

canonicalCKMCandidateHypotheses :
  List CKMCandidateHypothesis
canonicalCKMCandidateHypotheses =
  Vub_leading_order
  ∷ []

canonicalCKMUngrounded :
  List CKMQuantity
canonicalCKMUngrounded =
  Vcb
  ∷ gamma
  ∷ beta
  ∷ alpha
  ∷ []

data G7UnblockToken : Set where

g7UnblockTokenImpossibleHere :
  G7UnblockToken →
  ⊥
g7UnblockTokenImpossibleHere ()

record CKMFrontierGateReceipt : Set where
  field
    gate :
      CKMGate

    gateState :
      CKMGateState

    obligation :
      CKMGateObligation

    theoremEstablished :
      Bool

    theoremEstablishedIsFalse :
      theoremEstablished ≡ false

    blocksG7 :
      Bool

    blocksG7IsTrue :
      blocksG7 ≡ true

    affectedQuantities :
      List CKMQuantity

    currentQuantityStatus :
      CKMQuantityStatus

    candidateFormula :
      String

    blockerReason :
      String

open CKMFrontierGateReceipt public

gateAReceipt : CKMFrontierGateReceipt
gateAReceipt =
  record
    { gate =
        GateA
    ; gateState =
        openUntilTheorem
    ; obligation =
        DMinusSevenSelectionTheorem
    ; theoremEstablished =
        false
    ; theoremEstablishedIsFalse =
        refl
    ; blocksG7 =
        true
    ; blocksG7IsTrue =
        refl
    ; affectedQuantities =
        gamma
        ∷ beta
        ∷ []
    ; currentQuantityStatus =
        ungrounded
    ; candidateFormula =
        "D = -7 selection theorem"
    ; blockerReason =
        "Until the D=-7 selection theorem is proved, gamma and beta are ungrounded"
    }

gateBReceipt : CKMFrontierGateReceipt
gateBReceipt =
  record
    { gate =
        GateB
    ; gateState =
        openUntilIndependentDerivation
    ; obligation =
        IndependentVcbWithoutPDGAInput
    ; theoremEstablished =
        false
    ; theoremEstablishedIsFalse =
        refl
    ; blocksG7 =
        true
    ; blocksG7IsTrue =
        refl
    ; affectedQuantities =
        Vcb
        ∷ []
    ; currentQuantityStatus =
        pdgTautology
    ; candidateFormula =
        "|Vcb| approximately 1/N"
    ; blockerReason =
        "Independent |Vcb| derivation without the A=0.8086 PDG input is missing; the candidate |Vcb|~1/N has unidentified mapping"
    }

gateCReceipt : CKMFrontierGateReceipt
gateCReceipt =
  record
    { gate =
        GateC
    ; gateState =
        openUntilFullMatrixPhaseDerivation
    ; obligation =
        FullVubBeyondDownIdentity
    ; theoremEstablished =
        false
    ; theoremEstablishedIsFalse =
        refl
    ; blocksG7 =
        true
    ; blocksG7IsTrue =
        refl
    ; affectedQuantities =
        Vub
        ∷ []
    ; currentQuantityStatus =
        leadingOrderEstimate
    ; candidateFormula =
        "|Vub| leading order beyond U_d = I not yet promoted"
    ; blockerReason =
        "Next-order down-type rotation fails 1073 percent; full U_u^dagger U_d with phase structure is required"
    }

canonicalCKMFrontierGates :
  List CKMFrontierGateReceipt
canonicalCKMFrontierGates =
  gateAReceipt
  ∷ gateBReceipt
  ∷ gateCReceipt
  ∷ []

record CKMFrontierDefinitionReceipt : Setω where
  field
    G7 :
      CKMFrontierStatus

    G7IsBlocked :
      G7 ≡ blocked

    gateA :
      CKMFrontierGateReceipt

    gateAIsCanonical :
      gateA ≡ gateAReceipt

    gateB :
      CKMFrontierGateReceipt

    gateBIsCanonical :
      gateB ≡ gateBReceipt

    gateC :
      CKMFrontierGateReceipt

    gateCIsCanonical :
      gateC ≡ gateCReceipt

    gatesBeforeG7 :
      List CKMFrontierGateReceipt

    gatesBeforeG7AreCanonical :
      gatesBeforeG7 ≡ canonicalCKMFrontierGates

    allThreeGatesBlockG7 :
      Bool

    allThreeGatesBlockG7IsTrue :
      allThreeGatesBlockG7 ≡ true

    ckmProvedQuantities :
      List CKMQuantity

    ckmProvedQuantitiesAreCanonical :
      ckmProvedQuantities ≡ canonicalCKMProvedQuantities

    ckmCandidateHypotheses :
      List CKMCandidateHypothesis

    ckmCandidateHypothesesAreCanonical :
      ckmCandidateHypotheses ≡ canonicalCKMCandidateHypotheses

    ckmUngrounded :
      List CKMQuantity

    ckmUngroundedAreCanonical :
      ckmUngrounded ≡ canonicalCKMUngrounded

    vcbStatus :
      CKMQuantityStatus

    vcbStatusIsPdgTautology :
      vcbStatus ≡ pdgTautology

    vubStatus :
      CKMQuantityStatus

    vubStatusIsLeadingOrderEstimate :
      vubStatus ≡ leadingOrderEstimate

    dMinusSevenSelectionTheoremEstablished :
      Bool

    dMinusSevenSelectionTheoremEstablishedIsFalse :
      dMinusSevenSelectionTheoremEstablished ≡ false

    independentVcbDerivationEstablished :
      Bool

    independentVcbDerivationEstablishedIsFalse :
      independentVcbDerivationEstablished ≡ false

    fullVubMatrixPhaseDerivationEstablished :
      Bool

    fullVubMatrixPhaseDerivationEstablishedIsFalse :
      fullVubMatrixPhaseDerivationEstablished ≡ false

    downTypeNextOrderFailurePercent :
      Float

    downTypeNextOrderFailurePercentIsCanonical :
      downTypeNextOrderFailurePercent ≡ 1073.0

    g7UnblockTokens :
      List G7UnblockToken

    g7UnblockTokensAreEmpty :
      g7UnblockTokens ≡ []

    receiptBoundary :
      List String

open CKMFrontierDefinitionReceipt public

canonicalCKMFrontierDefinitionReceipt :
  CKMFrontierDefinitionReceipt
canonicalCKMFrontierDefinitionReceipt =
  record
    { G7 =
        blocked
    ; G7IsBlocked =
        refl
    ; gateA =
        gateAReceipt
    ; gateAIsCanonical =
        refl
    ; gateB =
        gateBReceipt
    ; gateBIsCanonical =
        refl
    ; gateC =
        gateCReceipt
    ; gateCIsCanonical =
        refl
    ; gatesBeforeG7 =
        canonicalCKMFrontierGates
    ; gatesBeforeG7AreCanonical =
        refl
    ; allThreeGatesBlockG7 =
        true
    ; allThreeGatesBlockG7IsTrue =
        refl
    ; ckmProvedQuantities =
        canonicalCKMProvedQuantities
    ; ckmProvedQuantitiesAreCanonical =
        refl
    ; ckmCandidateHypotheses =
        canonicalCKMCandidateHypotheses
    ; ckmCandidateHypothesesAreCanonical =
        refl
    ; ckmUngrounded =
        canonicalCKMUngrounded
    ; ckmUngroundedAreCanonical =
        refl
    ; vcbStatus =
        pdgTautology
    ; vcbStatusIsPdgTautology =
        refl
    ; vubStatus =
        leadingOrderEstimate
    ; vubStatusIsLeadingOrderEstimate =
        refl
    ; dMinusSevenSelectionTheoremEstablished =
        false
    ; dMinusSevenSelectionTheoremEstablishedIsFalse =
        refl
    ; independentVcbDerivationEstablished =
        false
    ; independentVcbDerivationEstablishedIsFalse =
        refl
    ; fullVubMatrixPhaseDerivationEstablished =
        false
    ; fullVubMatrixPhaseDerivationEstablishedIsFalse =
        refl
    ; downTypeNextOrderFailurePercent =
        1073.0
    ; downTypeNextOrderFailurePercentIsCanonical =
        refl
    ; g7UnblockTokens =
        []
    ; g7UnblockTokensAreEmpty =
        refl
    ; receiptBoundary =
        "G7 remains blocked by Gate A, Gate B, and Gate C"
        ∷ "Gate A requires the D=-7 selection theorem; gamma, beta, and hence alpha remain ungrounded until then"
        ∷ "Gate B requires an independent |Vcb| derivation without A=0.8086 PDG input; |Vcb| is currently a PDG tautology"
        ∷ "Gate C requires full U_u^dagger U_d with phase structure; the Vub row remains a leading-order estimate"
        ∷ "ckmProvedQuantities=[lambda], ckmCandidateHypotheses=[Vub_leading_order], ckmUngrounded=[Vcb,gamma,beta,alpha]"
        ∷ []
    }

canonicalG7Blocked :
  G7 canonicalCKMFrontierDefinitionReceipt ≡ blocked
canonicalG7Blocked =
  refl

canonicalCKMFrontierProvedQuantities :
  ckmProvedQuantities canonicalCKMFrontierDefinitionReceipt
  ≡
  lambda
  ∷ []
canonicalCKMFrontierProvedQuantities =
  refl

canonicalCKMFrontierCandidateHypotheses :
  ckmCandidateHypotheses canonicalCKMFrontierDefinitionReceipt
  ≡
  Vub_leading_order
  ∷ []
canonicalCKMFrontierCandidateHypotheses =
  refl

canonicalCKMFrontierUngrounded :
  ckmUngrounded canonicalCKMFrontierDefinitionReceipt
  ≡
  Vcb
  ∷ gamma
  ∷ beta
  ∷ alpha
  ∷ []
canonicalCKMFrontierUngrounded =
  refl

canonicalCKMFrontierNoUnblockToken :
  G7UnblockToken →
  ⊥
canonicalCKMFrontierNoUnblockToken =
  g7UnblockTokenImpossibleHere
