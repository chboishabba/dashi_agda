module DASHI.Reasoning.E6MinusculeFirstTitsWeightBasisBridgeExact where

------------------------------------------------------------------------
-- E6 MINUSCULE-27 WEIGHT ACTION -> FIRST-TITS 27 BASIS-LABEL BRIDGE
--
-- The stacked exceptional branch already owns two independent ingredients:
--
-- 1. `E6Ternary27FullSameActionReceiptExact` records the complete 51,840-
--    element E6 matrix/permutation same-action receipt on raw ternary-27;
-- 2. `Ternary27FirstTitsHeisenbergSchlafliBidiExact` identifies the literal
--    first-Tits M3^3 basis slots two-sidedly with that same ternary-27 / 6+15+6
--    Schlaefli carrier.
--
-- The new exact finite audit
--
--   scripts/check_e6_minuscule_first_tits_basis_bridge.py
--
-- independently reconstructs the E8->E6 projected minuscule 27 and the
-- first-Tits A2^3 Cartan weights. Both give the same 16-regular 216-edge weight
-- graph. A deterministic graph isomorphism transports the six E6 generating
-- reflections onto the literal first-Tits basis labels and regenerates the full
-- 51,840-element permutation image.
--
-- This materially closes the FINITE WEIGHT/BASIS-LABEL seam.  It still does
-- not construct chosen linear Weyl representatives on the rational Albert
-- vector space.  Each one-dimensional weight space may acquire a nonzero
-- scalar under a chosen representative, and those scalars must satisfy the
-- representation cocycle/composition law.  That scalar lift is the remaining
-- representation-level intertwiner, not another 27-point bijection.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.E6Ternary27FullSameActionReceiptExact as FullE6
import DASHI.Reasoning.Ternary27FirstTitsHeisenbergSchlafliBidiExact as TitsChart

record E6MinusculeFirstTitsExecutionReceipt : Set where
  constructor e6-minuscule-first-tits-execution-receipt
  field
    finiteWeightCount : Nat
    firstTitsBasisLabelCount : Nat
    rootDifferenceDegree : Nat
    rootDifferenceEdgeCount : Nat
    generatingReflectionCount : Nat
    generatedPermutationGroupOrder : Nat
    deterministicGraphIsomorphismComputed : Bool
    transportedGeneratorsPreserveFirstTitsWeightGraph : Bool
    transportedGeneratorsRegenerateFullE6PermutationImage : Bool
    pythonExecutionCountsAsAgdaKernelProof : Bool
open E6MinusculeFirstTitsExecutionReceipt public

canonicalE6MinusculeFirstTitsExecutionReceipt :
  E6MinusculeFirstTitsExecutionReceipt
canonicalE6MinusculeFirstTitsExecutionReceipt =
  e6-minuscule-first-tits-execution-receipt
    27 27 16 216 6 51840
    true true true false

record WeightSpaceScalarLift : Set₁ where
  field
    WeylElement : Set
    WeightLabel : Set
    Scalar : Set
    multiplyScalar : Scalar → Scalar → Scalar
    oneScalar : Scalar
    weightAction : WeylElement → WeightLabel → WeightLabel
    scalarAction : WeylElement → WeightLabel → Scalar
    composeWeyl : WeylElement → WeylElement → WeylElement
    scalarCocycle :
      (g h : WeylElement) (w : WeightLabel) →
      scalarAction (composeWeyl g h) w
      ≡ multiplyScalar
          (scalarAction g (weightAction h w))
          (scalarAction h w)
open WeightSpaceScalarLift public

record E6FirstTitsWeightBasisBoundary : Set where
  constructor e6-first-tits-weight-basis-boundary
  field
    rawTernaryFullE6SameActionSourceWritten : Bool
    firstTitsBasisTernaryChartTwoSided : Bool
    minusculeFirstTitsWeightGraphIsomorphismPaidAtExecutionGrade : Bool
    sixGeneratorActionTransportPaidAtExecutionGrade : Bool
    full51840PermutationImageOnFirstTitsLabelsPaidAtExecutionGrade : Bool
    finiteWeightBasisLabelBridgePaid : Bool
    linearWeightSpaceScalarLiftTyped : Bool
    chosenLinearWeylRepresentativesPaid : Bool
    scalarCocyclePaid : Bool
    fullAlbertE6RepresentationIntertwinerPaid : Bool
    note : String
open E6FirstTitsWeightBasisBoundary public

canonicalE6FirstTitsWeightBasisBoundary : E6FirstTitsWeightBasisBoundary
canonicalE6FirstTitsWeightBasisBoundary =
  e6-first-tits-weight-basis-boundary
    FullE6.canonicalFullSameActionBoundary.leanFull51840MatrixPermutationSyncSourceWritten
    TitsChart.canonicalFirstTitsHeisenbergSchlafliBoundary.composedChartsTwoSided
    true true true true true
    false false false
    "The finite E6 minuscule action is now transported all the way onto literal first-Tits M3^3 basis labels at execution grade, regenerating the 51,840-element permutation image. The surviving representation seam is only the nonzero scalar/phase assigned to each one-dimensional weight-space transport by chosen linear Weyl representatives, together with its composition cocycle and Albert-action identification."
