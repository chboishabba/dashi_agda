module DASHI.Physics.QFT.U1YFromCMCharacterReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.FiniteDHRAbelianReconstructionReceipt as FiniteDHR

------------------------------------------------------------------------
-- U(1)_Y-from-CM-character diagnostic receipt.
--
-- This receipt records the finite abelian CM-character candidate visible in
-- Z/4 x Z/6 x Z/2.  It is a diagnostic finite Z/3 character inside the Z/6
-- factor, not a derivation of the continuous U(1)_Y embedding or of exact
-- Standard Model hypercharge assignments.

data CMHyperchargeDenominatorDiagnostic : Set where
  hyperchargeMultiplesOfOneThird :
    CMHyperchargeDenominatorDiagnostic

data U1YFiniteCandidateSubgroup : Set where
  z3SubgroupOfZ6 :
    U1YFiniteCandidateSubgroup

data U1YContinuousEmbeddingStatus : Set where
  continuousU1EmbeddingOpen :
    U1YContinuousEmbeddingStatus

data U1YHyperchargeLabel : Set where
  qLHyperchargeOneThirdCandidate :
    U1YHyperchargeLabel

  uRHyperchargeFourThirdsRequiresContinuousNormalisation :
    U1YHyperchargeLabel

  dRHyperchargeMinusTwoThirdsRequiresContinuousNormalisation :
    U1YHyperchargeLabel

canonicalU1YHyperchargeLabels :
  List U1YHyperchargeLabel
canonicalU1YHyperchargeLabels =
  qLHyperchargeOneThirdCandidate
  ∷ uRHyperchargeFourThirdsRequiresContinuousNormalisation
  ∷ dRHyperchargeMinusTwoThirdsRequiresContinuousNormalisation
  ∷ []

u1YHyperchargeDisplayLabel :
  U1YHyperchargeLabel →
  String
u1YHyperchargeDisplayLabel qLHyperchargeOneThirdCandidate =
  "Q_L Y=1/3 candidate"
u1YHyperchargeDisplayLabel uRHyperchargeFourThirdsRequiresContinuousNormalisation =
  "u_R Y=4/3 requires continuous U1 normalization"
u1YHyperchargeDisplayLabel dRHyperchargeMinusTwoThirdsRequiresContinuousNormalisation =
  "d_R Y=-2/3 requires continuous U1 normalization"

finiteCMDualGroupLabel : String
finiteCMDualGroupLabel =
  "Z/4 x Z/6 x Z/2"

finiteCMDualGroupLCMLabel : String
finiteCMDualGroupLCMLabel =
  "lcm(4,6,2)=12"

u1YCandidateSubgroupLabel : String
u1YCandidateSubgroupLabel =
  "Z/3 subgroup of the Z/6 CM-character factor"

u1YDiagnosticBoundaryLabel : String
u1YDiagnosticBoundaryLabel =
  "Finite Z/3 CM-character candidate only; continuous U1_Y embedding and exact SM hypercharges remain open"

record U1YFromCMCharacterReceipt : Setω where
  field
    finiteDHRAbelianReceipt :
      FiniteDHR.FiniteDHRAbelianReconstructionReceipt

    finiteDHRAbelianReceiptReferenced :
      Bool

    finiteDHRAbelianReceiptReferencedIsTrue :
      finiteDHRAbelianReceiptReferenced ≡ true

    cmFiniteGroupLabel :
      String

    cmFiniteGroupLabelIsCanonical :
      cmFiniteGroupLabel ≡ finiteCMDualGroupLabel

    z4FactorOrder :
      Nat

    z4FactorOrderIsFour :
      z4FactorOrder ≡ FiniteDHR.finiteDHRAbelianDualFactorOrder
        FiniteDHR.z4CMConductorFactor

    z6FactorOrder :
      Nat

    z6FactorOrderIsSix :
      z6FactorOrder ≡ FiniteDHR.finiteDHRAbelianDualFactorOrder
        FiniteDHR.z6CMVolumeFactor

    z2FactorOrder :
      Nat

    z2FactorOrderIsTwo :
      z2FactorOrder ≡ FiniteDHR.finiteDHRAbelianDualFactorOrder
        FiniteDHR.z2ParityFactor

    cmFiniteGroupLCM :
      Nat

    cmFiniteGroupLCMIsTwelve :
      cmFiniteGroupLCM ≡ 12

    cmFiniteGroupLCMStatement :
      String

    cmFiniteGroupLCMStatementIsCanonical :
      cmFiniteGroupLCMStatement ≡ finiteCMDualGroupLCMLabel

    hyperchargeDenominatorDiagnostic :
      CMHyperchargeDenominatorDiagnostic

    hyperchargeDenominatorDiagnosticIsOneThird :
      hyperchargeDenominatorDiagnostic ≡ hyperchargeMultiplesOfOneThird

    hyperchargesMultiplesOfOneThird :
      Bool

    hyperchargesMultiplesOfOneThirdIsTrue :
      hyperchargesMultiplesOfOneThird ≡ true

    candidateSubgroup :
      U1YFiniteCandidateSubgroup

    candidateSubgroupIsZ3InsideZ6 :
      candidateSubgroup ≡ z3SubgroupOfZ6

    candidateSubgroupLabel :
      String

    candidateSubgroupLabelIsCanonical :
      candidateSubgroupLabel ≡ u1YCandidateSubgroupLabel

    discreteCharacterCandidate :
      Bool

    discreteCharacterCandidateIsTrue :
      discreteCharacterCandidate ≡ true

    continuousEmbeddingStatus :
      U1YContinuousEmbeddingStatus

    continuousEmbeddingStatusIsOpen :
      continuousEmbeddingStatus ≡ continuousU1EmbeddingOpen

    continuousU1EmbeddingConstructed :
      Bool

    continuousU1EmbeddingConstructedIsFalse :
      continuousU1EmbeddingConstructed ≡ false

    qLHyperchargeLabel :
      String

    qLHyperchargeLabelIsCanonical :
      qLHyperchargeLabel
      ≡
      u1YHyperchargeDisplayLabel qLHyperchargeOneThirdCandidate

    uRHyperchargeLabel :
      String

    uRHyperchargeLabelIsCanonical :
      uRHyperchargeLabel
      ≡
      u1YHyperchargeDisplayLabel
        uRHyperchargeFourThirdsRequiresContinuousNormalisation

    dRHyperchargeLabel :
      String

    dRHyperchargeLabelIsCanonical :
      dRHyperchargeLabel
      ≡
      u1YHyperchargeDisplayLabel
        dRHyperchargeMinusTwoThirdsRequiresContinuousNormalisation

    hyperchargeLabels :
      List U1YHyperchargeLabel

    hyperchargeLabelsAreCanonical :
      hyperchargeLabels ≡ canonicalU1YHyperchargeLabels

    exactHyperchargeAssignmentDerived :
      Bool

    exactHyperchargeAssignmentDerivedIsFalse :
      exactHyperchargeAssignmentDerived ≡ false

    exactStandardModelHyperchargeMatched :
      Bool

    exactStandardModelHyperchargeMatchedIsFalse :
      exactStandardModelHyperchargeMatched ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    diagnosticBoundary :
      String

    diagnosticBoundaryIsCanonical :
      diagnosticBoundary ≡ u1YDiagnosticBoundaryLabel

    receiptBoundary :
      List String

open U1YFromCMCharacterReceipt public

canonicalU1YFromCMCharacterReceipt :
  U1YFromCMCharacterReceipt
canonicalU1YFromCMCharacterReceipt =
  record
    { finiteDHRAbelianReceipt =
        FiniteDHR.canonicalFiniteDHRAbelianReconstructionReceipt
    ; finiteDHRAbelianReceiptReferenced =
        true
    ; finiteDHRAbelianReceiptReferencedIsTrue =
        refl
    ; cmFiniteGroupLabel =
        finiteCMDualGroupLabel
    ; cmFiniteGroupLabelIsCanonical =
        refl
    ; z4FactorOrder =
        4
    ; z4FactorOrderIsFour =
        refl
    ; z6FactorOrder =
        6
    ; z6FactorOrderIsSix =
        refl
    ; z2FactorOrder =
        2
    ; z2FactorOrderIsTwo =
        refl
    ; cmFiniteGroupLCM =
        12
    ; cmFiniteGroupLCMIsTwelve =
        refl
    ; cmFiniteGroupLCMStatement =
        finiteCMDualGroupLCMLabel
    ; cmFiniteGroupLCMStatementIsCanonical =
        refl
    ; hyperchargeDenominatorDiagnostic =
        hyperchargeMultiplesOfOneThird
    ; hyperchargeDenominatorDiagnosticIsOneThird =
        refl
    ; hyperchargesMultiplesOfOneThird =
        true
    ; hyperchargesMultiplesOfOneThirdIsTrue =
        refl
    ; candidateSubgroup =
        z3SubgroupOfZ6
    ; candidateSubgroupIsZ3InsideZ6 =
        refl
    ; candidateSubgroupLabel =
        u1YCandidateSubgroupLabel
    ; candidateSubgroupLabelIsCanonical =
        refl
    ; discreteCharacterCandidate =
        true
    ; discreteCharacterCandidateIsTrue =
        refl
    ; continuousEmbeddingStatus =
        continuousU1EmbeddingOpen
    ; continuousEmbeddingStatusIsOpen =
        refl
    ; continuousU1EmbeddingConstructed =
        false
    ; continuousU1EmbeddingConstructedIsFalse =
        refl
    ; qLHyperchargeLabel =
        "Q_L Y=1/3 candidate"
    ; qLHyperchargeLabelIsCanonical =
        refl
    ; uRHyperchargeLabel =
        "u_R Y=4/3 requires continuous U1 normalization"
    ; uRHyperchargeLabelIsCanonical =
        refl
    ; dRHyperchargeLabel =
        "d_R Y=-2/3 requires continuous U1 normalization"
    ; dRHyperchargeLabelIsCanonical =
        refl
    ; hyperchargeLabels =
        canonicalU1YHyperchargeLabels
    ; hyperchargeLabelsAreCanonical =
        refl
    ; exactHyperchargeAssignmentDerived =
        false
    ; exactHyperchargeAssignmentDerivedIsFalse =
        refl
    ; exactStandardModelHyperchargeMatched =
        false
    ; exactStandardModelHyperchargeMatchedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; diagnosticBoundary =
        u1YDiagnosticBoundaryLabel
    ; diagnosticBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        "The finite CM-character group is recorded as Z/4 x Z/6 x Z/2 with lcm 12"
        ∷ "The U1_Y diagnostic candidate is the Z/3 subgroup inside the Z/6 factor"
        ∷ "Hypercharges are recorded only as multiples-of-1/3 diagnostic labels"
        ∷ "Q_L has the finite Y=1/3 candidate label"
        ∷ "u_R Y=4/3 and d_R Y=-2/3 require continuous U1 normalization"
        ∷ "No continuous U1_Y embedding or exact Standard Model hypercharge assignment is derived here"
        ∷ []
    }

u1YFromCMCharacterDiscreteCandidateIsTrue :
  discreteCharacterCandidate canonicalU1YFromCMCharacterReceipt
  ≡
  true
u1YFromCMCharacterDiscreteCandidateIsTrue =
  refl

u1YFromCMCharacterContinuousEmbeddingIsFalse :
  continuousU1EmbeddingConstructed canonicalU1YFromCMCharacterReceipt
  ≡
  false
u1YFromCMCharacterContinuousEmbeddingIsFalse =
  refl

u1YFromCMCharacterExactAssignmentIsFalse :
  exactHyperchargeAssignmentDerived canonicalU1YFromCMCharacterReceipt
  ≡
  false
u1YFromCMCharacterExactAssignmentIsFalse =
  refl

u1YFromCMCharacterExactSMIsFalse :
  exactStandardModelPromoted canonicalU1YFromCMCharacterReceipt
  ≡
  false
u1YFromCMCharacterExactSMIsFalse =
  refl
