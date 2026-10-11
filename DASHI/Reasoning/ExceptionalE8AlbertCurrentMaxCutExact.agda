module DASHI.Reasoning.ExceptionalE8AlbertCurrentMaxCutExact where

------------------------------------------------------------------------
-- CURRENT EXCEPTIONAL E8 / ALBERT MAX-CUT
--
-- Fail-closed status surface spanning the source-native Agda rational Albert
-- algebra and the companion Lean structured-E8 / finite-Spin / F4 producers.
--
-- Agda natively owns:
--   * rational H3(O_Q), standard cubic and explicit Jordan product;
--   * commutativity, unit laws and the exceptional Jordan identity;
--   * explicit S3, signed-basis and Moufang-triality Albert automorphisms;
--   * the generic theorem that every [L_a,L_b] is a derivation;
--   * exact-rational executable diagnostics: derivation span/derived algebra
--     dimension 52, center 0, regular centralizer dimension 4, and compactness
--     / root-decomposition diagnostics.
--
-- Companion Lean now independently owns:
--   * intrinsic structured E8 root/Weyl data;
--   * explicit finite W(F4) Cartan/root datum (48 roots, rank four);
--   * four actual Spin/Tits Albert automorphisms and the exact 384 -> 192
--     quotient to the independently constructed W(D4) kernel;
--   * a native projective lift of one outer triality direction and an exhaustive
--     obstruction to the other inside the current 73728 signed-basis subgroup;
--   * an arbitrary-element inner-derivation theorem and exact local diagnostic
--     52 = 28 + 24 = 28 + 8+8+8 on the same rational Albert formulas.
--
-- The remaining exceptional wall is no longer generation-by-small-subgroups or
-- carrier arithmetic.  It is the explicit same-Lie-algebra/root-space bridge
-- from the concrete Albert derivation algebra to the independent F4 root datum,
-- plus the strictly stronger group recognition Aut(J)=F4=Stab_E6(1).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as Cubic
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as Product
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact as S3
import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismLawsExact as S3Laws
import DASHI.Mathematics.Algebra.RationalAlbertSignedBasisG2SubgroupExact as G2
import DASHI.Mathematics.Algebra.RationalAlbertMoufangTrialityAutomorphismExact as Triality
import DASHI.Mathematics.Algebra.RationalAlbertKnownGeneratorFamilyExact as Known
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationF4BoundaryExact as Deriv
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawExact as DerivLaw
import DASHI.Reasoning.AlbertF4LeanCrossProverMaxCutReceiptExact as LeanF4

record ExceptionalCurrentMaxCut : Set where
  constructor exceptional-current-max-cut
  field
    structuredE8RootCount : Nat
    structuredE8FullWeylDiagnosticOrder : Nat
    companionLeanIntrinsicGlueSourceWritten : Bool
    companionLeanE8CartanDetOneSourceWritten : Bool
    companionLeanE8CoxeterActionSourceWritten : Bool

    rationalAlbertHermitianCarrierPaid : Bool
    rationalAlbertCoordinateDimension27Paid : Bool
    rationalAlbertCubicNormPaid : Bool
    rationalAlbertJordanProductSourceWritten : Bool
    rationalAlbertCommutativitySourceWritten : Bool
    rationalAlbertUnitLawsSourceWritten : Bool
    rationalAlbertJordanIdentitySourceWritten : Bool
    rationalAlbertS3AutomorphismSubgroupSourceWritten : Bool
    rationalAlbertS3ProductCubicPreservationSourceWritten : Bool

    signedBasisG2SubgroupPaid : Bool
    selectedMoufangTrialityAutomorphismPaid : Bool
    selectedTrialityProductCubicPreservationPaid : Bool
    knownFiveAlbertGeneratorsBijectivePaid : Bool
    allInnerDerivationLawsSourceWritten : Bool
    innerDerivationDimension52DiagnosticPaid : Bool
    innerDerivationPerfectCenterlessDiagnosticPaid : Bool

    companionLeanFoldedWeylOrder1152Paid : Bool
    companionLeanF4Root48Rank4Paid : Bool
    companionLeanSpinCover384ToD4_192Paid : Bool
    companionLeanFourD4AlbertAutomorphismsPaid : Bool
    companionLeanG05ProjectiveOuterLiftPaid : Bool
    companionLeanG24CurrentSignedBasisObstructionPaid : Bool
    companionLeanDerivation52_28_24DiagnosticPaid : Bool

    agdaInnerDerivationSpan52KernelCertificatePaid : Bool
    agdaFormalComplexificationPaid : Bool
    agdaFormalRootSpaceDecompositionPaid : Bool
    sameLieAlgebraF4RecognitionPaid : Bool
    fullF4AutomorphismRecognitionPaid : Bool
    actualE6UnitStabilizerRecognitionPaid : Bool

    monsterNormalizerPhysicalRealizationPaid : Bool
    originalPuncturedT5SameObjectRecognitionPaid : Bool
    empiricalLilaInstantiationPaid : Bool
    boundaryNote : String
open ExceptionalCurrentMaxCut public

canonicalExceptionalCurrentMaxCut : ExceptionalCurrentMaxCut
canonicalExceptionalCurrentMaxCut =
  exceptional-current-max-cut
    240 696729600
    true true true
    true true true
    true true true true
    true true
    true true true true true true true
    true true true true true true true
    false false false false false false
    false false false
    "Structured E8 is source-written through the intrinsic glue/Coxeter root datum. Agda owns the actual rational Albert algebra and an arbitrary-element theorem that every inner commutator [L_a,L_b] is a derivation. Exact-rational diagnostics give a 52-dimensional perfect centerless derivation algebra with regular centralizer dimension four. Companion Lean independently pays the rank-four 48-root F4 datum, four actual D4/Spin Albert automorphisms with a 384-to-192 same-action quotient, a projective g05 outer lift, a current signed-basis obstruction for g24, and the exact-rational 52=28+24 triality diagnostic. The live wall is the formal complexified root-space/same-Lie-algebra bridge and then Aut(J)=F4=Stab_E6(1); neither dimension 52 nor root count 48 manufactures that bridge."
