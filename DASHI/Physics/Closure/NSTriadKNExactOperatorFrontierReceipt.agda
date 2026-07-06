module DASHI.Physics.Closure.NSTriadKNExactOperatorFrontierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceOperatorReceipt as PairIncidence
import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormulaReceipt as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecompositionReceipt as ProfileDecomposition
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileBounds as ProfileBounds
import DASHI.Physics.Closure.NSTriadKNForcedTailWeightedProductBoundReceipt as ForcedTail
import DASHI.Physics.Closure.NSTriadKNMixedTailDiagonalResidueBridgeReceipt as DiagonalResidue
import DASHI.Physics.Closure.NSTriadKNMixedTailBKMProjectionSmallnessReceipt as BKMProjection
import DASHI.Physics.Closure.NSShahmurovAxisymmetricReductionExternalReceipt as Shahmurov

------------------------------------------------------------------------
-- Fail-closed frontier receipt for the exact scripted mixed-tail lane.
--
-- This receipt records the current live sequencing after the sampled-object /
-- bare-proxy split was resolved: the exact scripted pair-incidence operator is
-- the only live Schur object, the profile-independent C/N theorem for that
-- exact object is still open, SchurResidueScale remains downstream of that
-- gate, and the BKM/residence bridge remains open after the projection step.

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed frontier receipt for the NS triad exact scripted operator, Schur residue scale, and BKM/residence bridge."

canonicalDocPath : String
canonicalDocPath =
  "docs/ns_triad_kn_exact_operator_frontier.md"

canonicalReadoutText : String
canonicalReadoutText =
  "Frontier status: the exact scripted pair-incidence operator is the only live mixed-tail Schur object. Its repeated-pair kernel formula is fixed, the structural four-profile decomposition is closed, and the forced-tail, adversarial, and transition profiles are now closed locally via dependency-honest closure bridges. The first still-open Stage 3 profile theorem is therefore the residual weighted-product bound. The first still-open global theorem is the profile-wise weighted Schur product closure R_N(w_N) * C_N(w_N) <= C^2 / N^2 implying ||L_FT,script^N||_op <= C / N. That global bound is still open. Therefore SchurResidueScale remains open at the residue-transfer step, and the BKM/residence bridge remains open at the structural projection plus trajectory/residence assembly step."

canonicalOperatorTheoremTarget : String
canonicalOperatorTheoremTarget =
  PairIncidence.canonicalTheoremTarget

canonicalSchurResidueTarget : String
canonicalSchurResidueTarget =
  "q_gap(N) >= c_gap / N^2"

canonicalBKMResidenceTarget : String
canonicalBKMResidenceTarget =
  "structural BKM projection smallness + residence-time exclusion"

record NSTriadKNExactOperatorFrontierReceipt : Setω where
  constructor mkNSTriadKNExactOperatorFrontierReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNExactOperatorFrontierReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    docPath : String
    docPathIsCanonical :
      docPath ≡ canonicalDocPath

    pairIncidenceReceiptName : String
    pairIncidenceReceiptNameIsCanonical :
      pairIncidenceReceiptName ≡ "NSTriadKNPairIncidenceOperatorReceipt"

    pairIncidenceReadoutText : String
    pairIncidenceReadoutTextIsCanonical :
      pairIncidenceReadoutText ≡ PairIncidence.canonicalReadoutText

    kernelFormulaReadoutText : String
    kernelFormulaReadoutTextIsCanonical :
      kernelFormulaReadoutText ≡ KernelFormula.canonicalReadoutText

    profileDecompositionReadoutText : String
    profileDecompositionReadoutTextIsCanonical :
      profileDecompositionReadoutText ≡
        ProfileDecomposition.canonicalReadoutText

    profileBoundsReadoutText : String
    profileBoundsReadoutTextIsCanonical :
      profileBoundsReadoutText ≡ ProfileBounds.canonicalReadoutText

    forcedTailWitnessReadoutText : String
    forcedTailWitnessReadoutTextIsCanonical :
      forcedTailWitnessReadoutText ≡ ForcedTail.canonicalReadoutText

    diagonalResidueReadoutText : String
    diagonalResidueReadoutTextIsCanonical :
      diagonalResidueReadoutText ≡ DiagonalResidue.canonicalReadoutText

    bkmProjectionReadoutText : String
    bkmProjectionReadoutTextIsCanonical :
      bkmProjectionReadoutText ≡ BKMProjection.canonicalReadoutText

    shahmurovReadoutText : String
    shahmurovReadoutTextIsCanonical :
      shahmurovReadoutText ≡ Shahmurov.canonicalReadoutText

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    operatorTheoremTarget : String
    operatorTheoremTargetIsCanonical :
      operatorTheoremTarget ≡ canonicalOperatorTheoremTarget

    weightedSchurProductRouteStated : Bool
    weightedSchurProductRouteStatedIsTrue :
      weightedSchurProductRouteStated ≡ true

    pairIncidenceKernelFormulaDerived : Bool
    pairIncidenceKernelFormulaDerivedIsTrue :
      pairIncidenceKernelFormulaDerived ≡ true

    profileDecompositionSurfaceImplemented : Bool
    profileDecompositionSurfaceImplementedIsTrue :
      profileDecompositionSurfaceImplemented ≡ true

    profileBoundsSurfaceImplemented : Bool
    profileBoundsSurfaceImplementedIsTrue :
      profileBoundsSurfaceImplemented ≡ true

    sampledForcedTailWitnessInstalled : Bool
    sampledForcedTailWitnessInstalledIsTrue :
      sampledForcedTailWitnessInstalled ≡ true

    schurResidueTarget : String
    schurResidueTargetIsCanonical :
      schurResidueTarget ≡ canonicalSchurResidueTarget

    bkmResidenceTarget : String
    bkmResidenceTargetIsCanonical :
      bkmResidenceTarget ≡ canonicalBKMResidenceTarget

    exactOperatorCanonicalized : Bool
    exactOperatorCanonicalizedIsTrue :
      exactOperatorCanonicalized ≡ true

    uniformProfileIndependentBoundClosed : Bool
    uniformProfileIndependentBoundClosedIsFalse :
      uniformProfileIndependentBoundClosed ≡ false

    schurResidueScaleClosed : Bool
    schurResidueScaleClosedIsFalse :
      schurResidueScaleClosed ≡ false

    bkmProjectionSmallnessClosed : Bool
    bkmProjectionSmallnessClosedIsFalse :
      bkmProjectionSmallnessClosed ≡ false

    residenceTimeExclusionClosed : Bool
    residenceTimeExclusionClosedIsFalse :
      residenceTimeExclusionClosed ≡ false

    bkmResidenceBridgeClosed : Bool
    bkmResidenceBridgeClosedIsFalse :
      bkmResidenceBridgeClosed ≡ false

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    bkmExclusionProved : Bool
    bkmExclusionProvedIsFalse :
      bkmExclusionProved ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNExactOperatorFrontierReceipt public

canonicalNSTriadKNExactOperatorFrontierReceipt :
  NSTriadKNExactOperatorFrontierReceipt
canonicalNSTriadKNExactOperatorFrontierReceipt =
  mkNSTriadKNExactOperatorFrontierReceipt
    "NSTriadKNExactOperatorFrontierReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalDocPath
    refl
    "NSTriadKNPairIncidenceOperatorReceipt"
    refl
    PairIncidence.canonicalReadoutText
    refl
    KernelFormula.canonicalReadoutText
    refl
    ProfileDecomposition.canonicalReadoutText
    refl
    ProfileBounds.canonicalReadoutText
    refl
    ForcedTail.canonicalReadoutText
    refl
    DiagonalResidue.canonicalReadoutText
    refl
    BKMProjection.canonicalReadoutText
    refl
    Shahmurov.canonicalReadoutText
    refl
    canonicalReadoutText
    refl
    canonicalOperatorTheoremTarget
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    canonicalSchurResidueTarget
    refl
    canonicalBKMResidenceTarget
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
