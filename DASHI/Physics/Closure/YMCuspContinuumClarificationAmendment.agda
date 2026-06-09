module DASHI.Physics.Closure.YMCuspContinuumClarificationAmendment where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Continuum clarification for the cusp-universality receipt.
--
-- This amendment records the load-bearing Clay-relevance condition: the
-- cusp comparison is continuum-to-continuum.  The carrier cusp theory
-- discussed in the cusp-universality receipts is not a lattice
-- regularisation and does not claim an easier discrete mass-gap theorem.
-- It is a curvature-modified continuum Yang-Mills theory whose curvature
-- correction is suppressed as N^{-4}.

data CuspTheoryNature : Set where
  continuumQFTNotLattice :
    CuspTheoryNature

data CuspComparisonKind : Set where
  continuumToContinuumComparison :
    CuspComparisonKind

data CuspLagrangianModel : Set where
  flatYangMillsPlusCurvatureSuppressedCorrection :
    CuspLagrangianModel

data CuspMassGapBiconditionalStatus : Set where
  clayRelevantOnlyAsContinuumComparison :
    CuspMassGapBiconditionalStatus

data ClayPromotionToken : Set where

clayPromotionImpossibleHere :
  ClayPromotionToken →
  ⊥
clayPromotionImpossibleHere ()

curvatureSuppressionStatement : String
curvatureSuppressionStatement =
  "The cusp carrier YM theory is a continuum QFT with L_cusp = L_flat + kappa(N) R(g_cusp) Tr(F^2), where kappa(N)=C0/N^4 tends to zero."

continuumComparisonStatement : String
continuumComparisonStatement =
  "Both M_gap^cusp(N) and M_gap^flat are continuum QFT quantities; the comparison is not a lattice regularisation argument."

biconditionalScopeStatement : String
biconditionalScopeStatement =
  "The biconditional M_gap^cusp(N)>0 iff M_gap^flat>0 is Clay-relevant only under this continuum-to-continuum reading."

record YMCuspContinuumClarificationAmendment : Set where
  field
    cuspTheoryNature :
      CuspTheoryNature

    cuspTheoryNatureIsContinuum :
      cuspTheoryNature ≡ continuumQFTNotLattice

    comparisonKind :
      CuspComparisonKind

    comparisonKindIsContinuumToContinuum :
      comparisonKind ≡ continuumToContinuumComparison

    lagrangianModel :
      CuspLagrangianModel

    lagrangianModelIsFlatYMPlusCurvatureCorrection :
      lagrangianModel ≡ flatYangMillsPlusCurvatureSuppressedCorrection

    curvatureCoefficientScalesAsNMinus4 :
      Bool

    curvatureCoefficientScalesAsNMinus4IsTrue :
      curvatureCoefficientScalesAsNMinus4 ≡ true

    notALatticeRegularisation :
      Bool

    notALatticeRegularisationIsTrue :
      notALatticeRegularisation ≡ true

    massGapBiconditionalStatus :
      CuspMassGapBiconditionalStatus

    massGapBiconditionalStatusIsClayRelevantOnlyAsContinuum :
      massGapBiconditionalStatus ≡ clayRelevantOnlyAsContinuumComparison

    curvatureStatement :
      String

    curvatureStatementIsCanonical :
      curvatureStatement ≡ curvatureSuppressionStatement

    continuumStatement :
      String

    continuumStatementIsCanonical :
      continuumStatement ≡ continuumComparisonStatement

    biconditionalScope :
      String

    biconditionalScopeIsCanonical :
      biconditionalScope ≡ biconditionalScopeStatement

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

open YMCuspContinuumClarificationAmendment public

canonicalYMCuspContinuumClarificationAmendment :
  YMCuspContinuumClarificationAmendment
canonicalYMCuspContinuumClarificationAmendment =
  record
    { cuspTheoryNature =
        continuumQFTNotLattice
    ; cuspTheoryNatureIsContinuum =
        refl
    ; comparisonKind =
        continuumToContinuumComparison
    ; comparisonKindIsContinuumToContinuum =
        refl
    ; lagrangianModel =
        flatYangMillsPlusCurvatureSuppressedCorrection
    ; lagrangianModelIsFlatYMPlusCurvatureCorrection =
        refl
    ; curvatureCoefficientScalesAsNMinus4 =
        true
    ; curvatureCoefficientScalesAsNMinus4IsTrue =
        refl
    ; notALatticeRegularisation =
        true
    ; notALatticeRegularisationIsTrue =
        refl
    ; massGapBiconditionalStatus =
        clayRelevantOnlyAsContinuumComparison
    ; massGapBiconditionalStatusIsClayRelevantOnlyAsContinuum =
        refl
    ; curvatureStatement =
        curvatureSuppressionStatement
    ; curvatureStatementIsCanonical =
        refl
    ; continuumStatement =
        continuumComparisonStatement
    ; continuumStatementIsCanonical =
        refl
    ; biconditionalScope =
        biconditionalScopeStatement
    ; biconditionalScopeIsCanonical =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    }

ymCuspClarificationNotLattice :
  notALatticeRegularisation canonicalYMCuspContinuumClarificationAmendment
  ≡ true
ymCuspClarificationNotLattice =
  refl

ymCuspClarificationNoClayPromotion :
  clayYangMillsPromoted canonicalYMCuspContinuumClarificationAmendment
  ≡ false
ymCuspClarificationNoClayPromotion =
  refl
