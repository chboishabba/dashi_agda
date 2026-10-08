module DASHI.Reasoning.ExceptionalE8AlbertF4RootMaxCutExact where

------------------------------------------------------------------------
-- EXCEPTIONAL E8 / ALBERT / F4 ROOT-DECOMPOSITION MAX-CUT
--
-- This supersedes the earlier frontier that still listed "find F4 root data"
-- as open.  The programme now has, on the SAME rational Albert algebra:
--
-- * a literal 27-coordinate H_3(O_Q) Jordan algebra with unit and cubic norm;
-- * arbitrary inner-derivation law for [L_x,L_y] source-written in Agda;
-- * exact-rational diagnostics: 351 basis pairs, derivation span 52, derived
--   span 52, center 0;
-- * negative trace form full rank/positive on a selected 52-basis;
-- * deterministic regular centralizer dimension 4;
-- * complexified-adjoint diagnostic: 48 nonzero root spaces, 24 short + 24
--   long with length-squared ratio two and an explicit standard F4 Cartan;
-- * companion Lean independently owns the standard 48-root F4 root datum and
--   its Coxeter/Weyl action.
--
-- Therefore the remaining mathematical promotion is no longer type discovery.
-- It is the formal scalar-extension/root-space SAME-LIE-ALGEBRA theorem and
-- then the algebraic-group statement Aut(H_3(O)) = F4 (with rational-form
-- bookkeeping).  Full Spin(8) triality generation is one possible group-level
-- route, but is not required to keep the Lie-algebra recognition statement
-- honest.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ExceptionalE8AlbertCurrentMaxCutExact as Previous
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawExact as InnerLaw
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationF4BoundaryExact as Inner
import DASHI.Mathematics.Algebra.RationalAlbertF4RootDecompositionDiagnosticExact as Roots
import DASHI.Mathematics.Algebra.RationalAlbertF4CurrentMaxCutExact as F4
import DASHI.Mathematics.Algebra.RationalOctonionSignedBasisAutomorphismExact as SignedG2
import DASHI.Mathematics.Algebra.RationalAlbertMoufangTrialityAutomorphismExact as Triality
import DASHI.Mathematics.Algebra.RationalAlbertAutomorphismClosureExact as Closure

record ExceptionalF4RootMaxCut : Set where
  constructor exceptional-f4-root-max-cut
  field
    structuredE8WeylRootDatumPaid : Bool
    rationalAlbertJordanAlgebraPaid : Bool
    arbitraryInnerDerivationLawSourceWritten : Bool
    innerDerivationRank52ExactDiagnostic : Bool
    innerDerivationPerfectCenterlessExactDiagnostic : Bool
    negativeTraceCompactnessDiagnostic : Bool
    regularCentralizerRank4Diagnostic : Bool
    complexifiedRootCount48Diagnostic : Bool
    longShortTwentyFourTwentyFourDiagnostic : Bool
    standardF4CartanOnAlbertDerivationsDiagnostic : Bool
    companionLeanIndependentF4Root48Paid : Bool
    companionLeanF4CoxeterPaid : Bool
    signedBasisOctonionAutomorphismsPaid : Bool
    selectedMoufangTrialityPaid : Bool
    arbitraryKnownAutomorphismWordCompilerPaid : Bool

    formalComplexificationRootSpacesPaid : Bool
    sameLieAlgebraAsTypeF4Paid : Bool
    rationalFormClassificationPaid : Bool
    fullSpin8TrialityFamilyPaid : Bool
    fullAutAlbertEqualsF4Paid : Bool
    actualE6UnitStabilizerEqualsF4Paid : Bool

    monsterNormalizerPhysicalRealizationPaid : Bool
    originalPuncturedT5SameObjectPaid : Bool
    empiricalLilaInstantiationPaid : Bool
    note : String
open ExceptionalF4RootMaxCut public

canonicalExceptionalF4RootMaxCut : ExceptionalF4RootMaxCut
canonicalExceptionalF4RootMaxCut =
  exceptional-f4-root-max-cut
    true true true
    true true true true true true true
    true true true true true
    false false false false false false
    false false false
    "The concrete Albert derivation algebra now exhibits the full numerical/root-theoretic fingerprint of compact type F4 on the same 52-dimensional operator span, while companion Lean independently owns the abstract 48-root F4 datum. The remaining honest theorem is formal scalar extension/root-space identification and same-Lie-algebra recognition, followed by the algebraic-group Aut(J)=F4 and E6-unit-stabilizer weld. Monster normalizer realization, any new original-T5 recognition, and empirical LILA remain independent lanes."
