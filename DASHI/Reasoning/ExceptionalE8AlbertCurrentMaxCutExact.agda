module DASHI.Reasoning.ExceptionalE8AlbertCurrentMaxCutExact where

------------------------------------------------------------------------
-- CURRENT EXCEPTIONAL E8 / ALBERT MAX-CUT
--
-- Structured E8 (companion Lean) is source-written through an intrinsic
-- inverse-Cartan glue reflection and E8 Coxeter root datum on 240 roots.
--
-- Rational Albert (this Agda branch) now contains:
--   * H_3(O_Q) = Q^3 + O_Q^3, coordinate dimension 27;
--   * identity, trace and cubic norm;
--   * explicit Jordan product, commutativity, unit and Jordan identity;
--   * coordinate S3 automorphisms preserving product/cubic;
--   * two explicit octonion signed-monomial automorphism generators;
--   * exhaustive signed-basis runtime closure 1344;
--   * diagonal Albert lift, commuting with coordinate S3, combined runtime
--     automorphism subgroup order 8064;
--   * exact rational derivation system rank 677 in 729 unknowns, hence
--     dim Der(J)=52;
--   * all 351 inner commutators span exact rational rank 52.
--
-- Negative control:
-- a natural order-192 signed-monomial line stabilizer times the independent
-- coordinate S3 has order 1152, but this is NOT promoted to W(F4); the missing
-- ingredient is the nontrivial D4 triality action, not order alone.
--
-- Remaining exceptional-algebra wall:
--   source-native D4/Spin(8) triality (or equivalent Cartan/root recognition),
--   then identify Der(J) as Lie type F4 and Aut(J) as the corresponding F4
--   algebraic/Lie group.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.RationalAlbertF4CurrentMaxCutExact as F4Cut

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
    rationalAlbertJordanLawsSourceWritten : Bool
    rationalAlbertCoordinateS3AutomorphismsSourceWritten : Bool
    signedMonomialOctonionAutomorphismsSourceWritten : Bool
    signedMonomialClosure1344RuntimeChecked : Bool
    signedMonomialAlbertLiftSourceWritten : Bool
    explicitAlbertAutomorphismSubgroup8064RuntimeChecked : Bool
    derivationConstraintRank677RuntimeChecked : Bool
    derivationDimension52RuntimeChecked : Bool
    innerDerivationSpan52RuntimeChecked : Bool
    order1152RejectedAsWeylF4Recognition : Bool
    nontrivialD4TrialityPaid : Bool
    f4LieAlgebraRecognitionPaid : Bool
    fullF4AutomorphismRecognitionPaid : Bool
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
    true true true true true true
    true true true true
    true true true true
    false false false false false false
    "Structured E8 is closed at source level. The rational Albert algebra, cubic norm, Jordan laws, explicit S3 and signed-monomial automorphisms are source-written; exact rational runtime gives dim Der(J)=52 with inner span 52. The active exceptional wall is nontrivial D4/Spin(8) triality and Lie/root classification to identify Der(J) and Aut(J) as F4, not another cardinality match."
