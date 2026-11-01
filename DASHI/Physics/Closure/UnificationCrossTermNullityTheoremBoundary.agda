module DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary where

-- Boundary for the actual U-1a cross-term nullity theorem target.
--
-- Target:
--
--   G(s1 + s2) - G(s1) - G(s2) lies in the null class.
--
-- This file records the one honest live theorem shape that downstream U-1a
-- consumers need, while consuming the existing fail-closed child surfaces for
-- discriminant seeding, approximate-compatibility bookkeeping, the residual
-- PDE / Carleman intake, cross-term null class, null stability,
-- null-to-quotient equality transport, and modulo-null gluing linearity.
--
-- The honest candidate route is:
--
--   approximate compatibility
--   -> residual PDE / Carleman intake
--   -> cross-term nullity
--   -> modulo-null linearity
--   -> four-point / parallelogram / Jordan-von Neumann downstream.
--
-- This file does not prove the theorem and does not promote four-point
-- cancellation, parallelogram, quadratic emergence, or terminal unification.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary
  as U1a
import DASHI.Physics.Closure.UnificationCrossTermNullityDiscriminantBoundary
  as Discriminant
import DASHI.Physics.Closure.UnificationGluingCrossTermNullClassBoundary
  as CrossTerm
import DASHI.Physics.Closure.UnificationNullClassStabilityBoundary
  as NullStability
import DASHI.Physics.Closure.UnificationNullToQuotientEqualityTransportBoundary
  as NullTransport
import DASHI.Physics.Closure.UnificationGluingModuloNullLinearityCompositeBoundary
  as ModuloNull

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- The actual theorem target.

actualU1aCrossTerm :
  (V : U1a.AdmissibleDefectQuotientVBoundary) →
  U1a.GluingOperatorGBoundary V →
  (U1a.DefectQuotientV V → U1a.DefectQuotientV V) →
  U1a.DefectQuotientV V →
  U1a.DefectQuotientV V →
  U1a.DefectQuotientV V
actualU1aCrossTerm V G-boundary -V_ s1 s2 =
  U1a._+V_ V
    (U1a._+V_ V
      (U1a.G G-boundary (U1a._+V_ V s1 s2))
      (-V_ (U1a.G G-boundary s1)))
    (-V_ (U1a.G G-boundary s2))

record U1aCrossTermNullityTheoremTarget
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V) : Setω where
  field
    -V_ :
      U1a.DefectQuotientV V → U1a.DefectQuotientV V

    nullClass :
      U1a.DefectQuotientV V → Set

    theoremTarget :
      (s1 s2 : U1a.DefectQuotientV V) →
      nullClass (actualU1aCrossTerm V G-boundary -V_ s1 s2)

    theoremTargetText :
      String

    theoremTargetTextIsCanonical :
      theoremTargetText
      ≡ "forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2))"

open U1aCrossTermNullityTheoremTarget public

record U1aCrossTermNullityRepresentativeInvarianceObligation
  (V : U1a.AdmissibleDefectQuotientVBoundary)
  (G-boundary : U1a.GluingOperatorGBoundary V) : Setω where
  field
    representativeEquivalent :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      Set

    nullClass :
      U1a.DefectQuotientV V → Set

    representativeInvarianceTarget :
      (x y : U1a.DefectQuotientV V) →
      representativeEquivalent x y →
      nullClass x →
      nullClass y

    gluingRepresentativeInvarianceTarget :
      (x y : U1a.DefectQuotientV V) →
      representativeEquivalent x y →
      representativeEquivalent
        (U1a.G G-boundary x)
        (U1a.G G-boundary y)

open U1aCrossTermNullityRepresentativeInvarianceObligation public

------------------------------------------------------------------------
-- Imported support.

data UnificationCrossTermIntakeClause : Set where
  UCT1-residualPDESpecification :
    UnificationCrossTermIntakeClause

  UCT2-ellipticityOrParabolicityClass :
    UnificationCrossTermIntakeClause

  UCT3-CarlemanUniqueContinuationIntake :
    UnificationCrossTermIntakeClause

  UCT4-crossTermNullityTheoremTarget :
    UnificationCrossTermIntakeClause

canonicalUnificationCrossTermIntakeClauseLabel :
  UnificationCrossTermIntakeClause → String
canonicalUnificationCrossTermIntakeClauseLabel
  UCT1-residualPDESpecification =
  "UCT.1 residual PDE specification"
canonicalUnificationCrossTermIntakeClauseLabel
  UCT2-ellipticityOrParabolicityClass =
  "UCT.2 ellipticity/parabolicity class"
canonicalUnificationCrossTermIntakeClauseLabel
  UCT3-CarlemanUniqueContinuationIntake =
  "UCT.3 Carleman/unique-continuation intake"
canonicalUnificationCrossTermIntakeClauseLabel
  UCT4-crossTermNullityTheoremTarget =
  "UCT.4 cross-term nullity theorem target"

canonicalUnificationCrossTermIntakeClauseText :
  UnificationCrossTermIntakeClause → String
canonicalUnificationCrossTermIntakeClauseText
  UCT1-residualPDESpecification =
  "Specify the residual PDE satisfied by the gluing cross-term defect before any nullity claim."
canonicalUnificationCrossTermIntakeClauseText
  UCT2-ellipticityOrParabolicityClass =
  "Specify whether the residual PDE sits in the elliptic or parabolic class and record the operator regime."
canonicalUnificationCrossTermIntakeClauseText
  UCT3-CarlemanUniqueContinuationIntake =
  "Specify the Carleman/unique-continuation intake matched to the chosen PDE class before transporting to nullity."
canonicalUnificationCrossTermIntakeClauseText
  UCT4-crossTermNullityTheoremTarget =
  "Target theorem: forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2)), then hand off only to modulo-null consumers."

canonicalUnificationCrossTermIntakeAuthorityString :
  UnificationCrossTermIntakeClause → String
canonicalUnificationCrossTermIntakeAuthorityString
  UCT1-residualPDESpecification =
  "Authority required: an exact residual PDE statement for the unification cross-term defect."
canonicalUnificationCrossTermIntakeAuthorityString
  UCT2-ellipticityOrParabolicityClass =
  "Authority required: an operator-class witness fixing elliptic versus parabolic unique-continuation regime."
canonicalUnificationCrossTermIntakeAuthorityString
  UCT3-CarlemanUniqueContinuationIntake =
  "Authority required: a Carleman or unique-continuation theorem intake compatible with the recorded operator class."
canonicalUnificationCrossTermIntakeAuthorityString
  UCT4-crossTermNullityTheoremTarget =
  "Authority required: a theorem deriving cross-term nullity from the exact PDE and unique-continuation intake."

canonicalUnificationCrossTermIntakeBlockerName :
  UnificationCrossTermIntakeClause → String
canonicalUnificationCrossTermIntakeBlockerName
  UCT1-residualPDESpecification =
  "missing-residual-pde-specification"
canonicalUnificationCrossTermIntakeBlockerName
  UCT2-ellipticityOrParabolicityClass =
  "missing-elliptic-or-parabolic-class"
canonicalUnificationCrossTermIntakeBlockerName
  UCT3-CarlemanUniqueContinuationIntake =
  "missing-carleman-unique-continuation-intake"
canonicalUnificationCrossTermIntakeBlockerName
  UCT4-crossTermNullityTheoremTarget =
  "missing-cross-term-nullity-theorem"

record UnificationCrossTermIntakeClauseBoundary : Setω where
  field
    clause :
      UnificationCrossTermIntakeClause

    clauseLabel :
      String

    clauseLabelIsCanonical :
      clauseLabel ≡ canonicalUnificationCrossTermIntakeClauseLabel clause

    clauseText :
      String

    clauseTextIsCanonical :
      clauseText ≡ canonicalUnificationCrossTermIntakeClauseText clause

    importedAuthorityString :
      String

    importedAuthorityStringIsCanonical :
      importedAuthorityString
      ≡ canonicalUnificationCrossTermIntakeAuthorityString clause

    blockerName :
      String

    blockerNameIsCanonical :
      blockerName ≡ canonicalUnificationCrossTermIntakeBlockerName clause

    clauseRecorded :
      Bool

    clauseRecordedIsTrue :
      clauseRecorded ≡ true

    clauseImported :
      Bool

    clauseImportedIsFalse :
      clauseImported ≡ false

open UnificationCrossTermIntakeClauseBoundary public

mkUnificationCrossTermIntakeClauseBoundary :
  UnificationCrossTermIntakeClause →
  UnificationCrossTermIntakeClauseBoundary
mkUnificationCrossTermIntakeClauseBoundary clause =
  record
    { clause = clause
    ; clauseLabel = canonicalUnificationCrossTermIntakeClauseLabel clause
    ; clauseLabelIsCanonical = refl
    ; clauseText = canonicalUnificationCrossTermIntakeClauseText clause
    ; clauseTextIsCanonical = refl
    ; importedAuthorityString =
        canonicalUnificationCrossTermIntakeAuthorityString clause
    ; importedAuthorityStringIsCanonical = refl
    ; blockerName = canonicalUnificationCrossTermIntakeBlockerName clause
    ; blockerNameIsCanonical = refl
    ; clauseRecorded = true
    ; clauseRecordedIsTrue = refl
    ; clauseImported = false
    ; clauseImportedIsFalse = refl
    }

data UnificationCrossTermTheoremClause : Set where
  UCT1-residualPDESpecificationClause :
    UnificationCrossTermTheoremClause

  UCT2-ellipticityOrParabolicityClassClause :
    UnificationCrossTermTheoremClause

  UCT3-CarlemanUniqueContinuationIntakeClause :
    UnificationCrossTermTheoremClause

  UCT4-crossTermNullityTheoremClause :
    UnificationCrossTermTheoremClause

  UCT5-moduloNullLinearityConsumerClause :
    UnificationCrossTermTheoremClause

  UCT6-fourPointCancellationConsumerClause :
    UnificationCrossTermTheoremClause

  UCT7-parallelogramConsumerClause :
    UnificationCrossTermTheoremClause

  UCT8-jordanVonNeumannAdapterConsumerClause :
    UnificationCrossTermTheoremClause

canonicalUnificationCrossTermTheoremClauseLabel :
  UnificationCrossTermTheoremClause → String
canonicalUnificationCrossTermTheoremClauseLabel
  UCT1-residualPDESpecificationClause =
  "UCT.1 residual PDE specification"
canonicalUnificationCrossTermTheoremClauseLabel
  UCT2-ellipticityOrParabolicityClassClause =
  "UCT.2 ellipticity/parabolicity class"
canonicalUnificationCrossTermTheoremClauseLabel
  UCT3-CarlemanUniqueContinuationIntakeClause =
  "UCT.3 Carleman/unique-continuation intake"
canonicalUnificationCrossTermTheoremClauseLabel
  UCT4-crossTermNullityTheoremClause =
  "UCT.4 cross-term nullity theorem"
canonicalUnificationCrossTermTheoremClauseLabel
  UCT5-moduloNullLinearityConsumerClause =
  "UCT.5 modulo-null linearity consumer"
canonicalUnificationCrossTermTheoremClauseLabel
  UCT6-fourPointCancellationConsumerClause =
  "UCT.6 four-point cancellation consumer"
canonicalUnificationCrossTermTheoremClauseLabel
  UCT7-parallelogramConsumerClause =
  "UCT.7 parallelogram consumer"
canonicalUnificationCrossTermTheoremClauseLabel
  UCT8-jordanVonNeumannAdapterConsumerClause =
  "UCT.8 Jordan-von Neumann adapter consumer"

canonicalUnificationCrossTermTheoremClauseText :
  UnificationCrossTermTheoremClause → String
canonicalUnificationCrossTermTheoremClauseText
  UCT1-residualPDESpecificationClause =
  "UCT.1 exact intake: specify the residual PDE satisfied by c(s1,s2)=G(s1 +V s2) -V G(s1) -V G(s2) before any nullity or quotient claim."
canonicalUnificationCrossTermTheoremClauseText
  UCT2-ellipticityOrParabolicityClassClause =
  "UCT.2 exact intake: fix the elliptic or parabolic operator regime for the UCT.1 residual PDE and record the admissible unique-continuation class."
canonicalUnificationCrossTermTheoremClauseText
  UCT3-CarlemanUniqueContinuationIntakeClause =
  "UCT.3 exact intake: fix the Carleman/unique-continuation theorem input matched to UCT.2 and strong enough to force UCT.4 cross-term nullity."
canonicalUnificationCrossTermTheoremClauseText
  UCT4-crossTermNullityTheoremClause =
  "UCT.4 theorem text: forall s1 s2, nullClass (c(s1,s2)) where c(s1,s2)=G(s1 +V s2) -V G(s1) -V G(s2)."
canonicalUnificationCrossTermTheoremClauseText
  UCT5-moduloNullLinearityConsumerClause =
  "UCT.5 downstream consumer: consume UCT.4 only through fail-closed null-to-quotient transport into modulo-null gluing linearity."
canonicalUnificationCrossTermTheoremClauseText
  UCT6-fourPointCancellationConsumerClause =
  "UCT.6 downstream consumer: consume UCT.5 only through fail-closed four-point cancellation on the modulo-null side."
canonicalUnificationCrossTermTheoremClauseText
  UCT7-parallelogramConsumerClause =
  "UCT.7 downstream consumer: consume UCT.6 only through fail-closed parallelogram data."
canonicalUnificationCrossTermTheoremClauseText
  UCT8-jordanVonNeumannAdapterConsumerClause =
  "UCT.8 downstream consumer: consume UCT.7 only through fail-closed Jordan-von Neumann adapter surfaces on V/null."

canonicalUnificationCrossTermTheoremClauseBlockerName :
  UnificationCrossTermTheoremClause → String
canonicalUnificationCrossTermTheoremClauseBlockerName
  UCT1-residualPDESpecificationClause =
  "missing-uct1-residual-pde-specification"
canonicalUnificationCrossTermTheoremClauseBlockerName
  UCT2-ellipticityOrParabolicityClassClause =
  "missing-uct2-elliptic-or-parabolic-class"
canonicalUnificationCrossTermTheoremClauseBlockerName
  UCT3-CarlemanUniqueContinuationIntakeClause =
  "missing-uct3-carleman-unique-continuation-intake"
canonicalUnificationCrossTermTheoremClauseBlockerName
  UCT4-crossTermNullityTheoremClause =
  "missing-uct4-cross-term-nullity-theorem"
canonicalUnificationCrossTermTheoremClauseBlockerName
  UCT5-moduloNullLinearityConsumerClause =
  "missing-uct5-modulo-null-linearity-consumer"
canonicalUnificationCrossTermTheoremClauseBlockerName
  UCT6-fourPointCancellationConsumerClause =
  "missing-uct6-four-point-cancellation-consumer"
canonicalUnificationCrossTermTheoremClauseBlockerName
  UCT7-parallelogramConsumerClause =
  "missing-uct7-parallelogram-consumer"
canonicalUnificationCrossTermTheoremClauseBlockerName
  UCT8-jordanVonNeumannAdapterConsumerClause =
  "missing-uct8-jordan-von-neumann-adapter-consumer"

record UnificationCrossTermTheoremClauseBoundary : Setω where
  field
    clause :
      UnificationCrossTermTheoremClause

    clauseLabel :
      String

    clauseLabelIsCanonical :
      clauseLabel ≡ canonicalUnificationCrossTermTheoremClauseLabel clause

    clauseText :
      String

    clauseTextIsCanonical :
      clauseText ≡ canonicalUnificationCrossTermTheoremClauseText clause

    blockerName :
      String

    blockerNameIsCanonical :
      blockerName ≡ canonicalUnificationCrossTermTheoremClauseBlockerName clause

    clauseRecorded :
      Bool

    clauseRecordedIsTrue :
      clauseRecorded ≡ true

    clauseImported :
      Bool

    clauseImportedIsFalse :
      clauseImported ≡ false

open UnificationCrossTermTheoremClauseBoundary public

mkUnificationCrossTermTheoremClauseBoundary :
  UnificationCrossTermTheoremClause →
  UnificationCrossTermTheoremClauseBoundary
mkUnificationCrossTermTheoremClauseBoundary clause =
  record
    { clause = clause
    ; clauseLabel = canonicalUnificationCrossTermTheoremClauseLabel clause
    ; clauseLabelIsCanonical = refl
    ; clauseText = canonicalUnificationCrossTermTheoremClauseText clause
    ; clauseTextIsCanonical = refl
    ; blockerName = canonicalUnificationCrossTermTheoremClauseBlockerName clause
    ; blockerNameIsCanonical = refl
    ; clauseRecorded = true
    ; clauseRecordedIsTrue = refl
    ; clauseImported = false
    ; clauseImportedIsFalse = refl
    }

record CrossTermNullityExactGrammarBoundary : Setω where
  field
    uct1ResidualPDESpecificationClause :
      UnificationCrossTermTheoremClauseBoundary

    uct1ResidualPDESpecificationClauseIsCanonical :
      clause uct1ResidualPDESpecificationClause
      ≡ UCT1-residualPDESpecificationClause

    uct2EllipticityOrParabolicityClassClause :
      UnificationCrossTermTheoremClauseBoundary

    uct2EllipticityOrParabolicityClassClauseIsCanonical :
      clause uct2EllipticityOrParabolicityClassClause
      ≡ UCT2-ellipticityOrParabolicityClassClause

    uct3CarlemanUniqueContinuationIntakeClause :
      UnificationCrossTermTheoremClauseBoundary

    uct3CarlemanUniqueContinuationIntakeClauseIsCanonical :
      clause uct3CarlemanUniqueContinuationIntakeClause
      ≡ UCT3-CarlemanUniqueContinuationIntakeClause

    uct4CrossTermNullityTheoremClause :
      UnificationCrossTermTheoremClauseBoundary

    uct4CrossTermNullityTheoremClauseIsCanonical :
      clause uct4CrossTermNullityTheoremClause
      ≡ UCT4-crossTermNullityTheoremClause

    uct5ModuloNullLinearityConsumerClause :
      UnificationCrossTermTheoremClauseBoundary

    uct5ModuloNullLinearityConsumerClauseIsCanonical :
      clause uct5ModuloNullLinearityConsumerClause
      ≡ UCT5-moduloNullLinearityConsumerClause

    uct6FourPointCancellationConsumerClause :
      UnificationCrossTermTheoremClauseBoundary

    uct6FourPointCancellationConsumerClauseIsCanonical :
      clause uct6FourPointCancellationConsumerClause
      ≡ UCT6-fourPointCancellationConsumerClause

    uct7ParallelogramConsumerClause :
      UnificationCrossTermTheoremClauseBoundary

    uct7ParallelogramConsumerClauseIsCanonical :
      clause uct7ParallelogramConsumerClause
      ≡ UCT7-parallelogramConsumerClause

    uct8JordanVonNeumannAdapterConsumerClause :
      UnificationCrossTermTheoremClauseBoundary

    uct8JordanVonNeumannAdapterConsumerClauseIsCanonical :
      clause uct8JordanVonNeumannAdapterConsumerClause
      ≡ UCT8-jordanVonNeumannAdapterConsumerClause

    exactGrammarText :
      String

    exactGrammarTextIsCanonical :
      exactGrammarText
      ≡ "UCT.1 exact residual PDE for c(s1,s2) -> UCT.2 elliptic/parabolic operator class -> UCT.3 Carleman/unique-continuation intake -> UCT.4 cross-term nullity theorem -> UCT.5 modulo-null linearity consumer -> UCT.6 four-point cancellation consumer -> UCT.7 parallelogram consumer -> UCT.8 Jordan-von Neumann adapter consumer"

    theoremClauseCount :
      Nat

    theoremClauseCountIs8 :
      theoremClauseCount ≡ 8

open CrossTermNullityExactGrammarBoundary public

canonicalCrossTermNullityExactGrammarBoundary :
  CrossTermNullityExactGrammarBoundary
canonicalCrossTermNullityExactGrammarBoundary =
  record
    { uct1ResidualPDESpecificationClause =
        mkUnificationCrossTermTheoremClauseBoundary
          UCT1-residualPDESpecificationClause
    ; uct1ResidualPDESpecificationClauseIsCanonical =
        refl
    ; uct2EllipticityOrParabolicityClassClause =
        mkUnificationCrossTermTheoremClauseBoundary
          UCT2-ellipticityOrParabolicityClassClause
    ; uct2EllipticityOrParabolicityClassClauseIsCanonical =
        refl
    ; uct3CarlemanUniqueContinuationIntakeClause =
        mkUnificationCrossTermTheoremClauseBoundary
          UCT3-CarlemanUniqueContinuationIntakeClause
    ; uct3CarlemanUniqueContinuationIntakeClauseIsCanonical =
        refl
    ; uct4CrossTermNullityTheoremClause =
        mkUnificationCrossTermTheoremClauseBoundary
          UCT4-crossTermNullityTheoremClause
    ; uct4CrossTermNullityTheoremClauseIsCanonical =
        refl
    ; uct5ModuloNullLinearityConsumerClause =
        mkUnificationCrossTermTheoremClauseBoundary
          UCT5-moduloNullLinearityConsumerClause
    ; uct5ModuloNullLinearityConsumerClauseIsCanonical =
        refl
    ; uct6FourPointCancellationConsumerClause =
        mkUnificationCrossTermTheoremClauseBoundary
          UCT6-fourPointCancellationConsumerClause
    ; uct6FourPointCancellationConsumerClauseIsCanonical =
        refl
    ; uct7ParallelogramConsumerClause =
        mkUnificationCrossTermTheoremClauseBoundary
          UCT7-parallelogramConsumerClause
    ; uct7ParallelogramConsumerClauseIsCanonical =
        refl
    ; uct8JordanVonNeumannAdapterConsumerClause =
        mkUnificationCrossTermTheoremClauseBoundary
          UCT8-jordanVonNeumannAdapterConsumerClause
    ; uct8JordanVonNeumannAdapterConsumerClauseIsCanonical =
        refl
    ; exactGrammarText =
        "UCT.1 exact residual PDE for c(s1,s2) -> UCT.2 elliptic/parabolic operator class -> UCT.3 Carleman/unique-continuation intake -> UCT.4 cross-term nullity theorem -> UCT.5 modulo-null linearity consumer -> UCT.6 four-point cancellation consumer -> UCT.7 parallelogram consumer -> UCT.8 Jordan-von Neumann adapter consumer"
    ; exactGrammarTextIsCanonical =
        refl
    ; theoremClauseCount =
        8
    ; theoremClauseCountIs8 =
        refl
    }

record CrossTermNullityAnalyticIntakeBoundary : Setω where
  field
    approximateCompatibilityRouteText :
      String

    approximateCompatibilityRouteTextIsCanonical :
      approximateCompatibilityRouteText
      ≡ "approximate compatibility is the only recorded upstream route into the exact UCT.1-UCT.3 intake contract"

    uct1ResidualPDESpecification :
      UnificationCrossTermIntakeClauseBoundary

    uct1ResidualPDESpecificationIsCanonical :
      clause uct1ResidualPDESpecification
      ≡ UCT1-residualPDESpecification

    uct2EllipticityOrParabolicityClass :
      UnificationCrossTermIntakeClauseBoundary

    uct2EllipticityOrParabolicityClassIsCanonical :
      clause uct2EllipticityOrParabolicityClass
      ≡ UCT2-ellipticityOrParabolicityClass

    uct3CarlemanUniqueContinuationIntake :
      UnificationCrossTermIntakeClauseBoundary

    uct3CarlemanUniqueContinuationIntakeIsCanonical :
      clause uct3CarlemanUniqueContinuationIntake
      ≡ UCT3-CarlemanUniqueContinuationIntake

    uct4CrossTermNullityTheoremTarget :
      UnificationCrossTermIntakeClauseBoundary

    uct4CrossTermNullityTheoremTargetIsCanonical :
      clause uct4CrossTermNullityTheoremTarget
      ≡ UCT4-crossTermNullityTheoremTarget

    exactIntakeContractText :
      String

    exactIntakeContractTextIsCanonical :
      exactIntakeContractText
      ≡ "UCT.1 exact residual PDE for c(s1,s2) -> UCT.2 elliptic/parabolic operator class -> UCT.3 Carleman/unique-continuation intake -> UCT.4 cross-term nullity theorem target"

    downstreamRouteText :
      String

    downstreamRouteTextIsCanonical :
      downstreamRouteText
      ≡ "once UCT.4 is supplied, only the fail-closed downstream chain UCT.5 modulo-null -> UCT.6 four-point -> UCT.7 parallelogram -> UCT.8 Jordan-von Neumann may read it"

    approximateCompatibilityRecorded :
      Bool

    approximateCompatibilityRecordedIsTrue :
      approximateCompatibilityRecorded ≡ true

    residualPDERecorded :
      Bool

    residualPDERecordedIsTrue :
      residualPDERecorded ≡ true

    ellipticityOrParabolicityClassRecorded :
      Bool

    ellipticityOrParabolicityClassRecordedIsTrue :
      ellipticityOrParabolicityClassRecorded ≡ true

    carlemanIntakeRecorded :
      Bool

    carlemanIntakeRecordedIsTrue :
      carlemanIntakeRecorded ≡ true

    theoremTargetRecorded :
      Bool

    theoremTargetRecordedIsTrue :
      theoremTargetRecorded ≡ true

    moduloNullConsumerHandoffRecorded :
      Bool

    moduloNullConsumerHandoffRecordedIsTrue :
      moduloNullConsumerHandoffRecorded ≡ true

    residualPDEHypothesesSpecified :
      Bool

    residualPDEHypothesesSpecifiedIsFalse :
      residualPDEHypothesesSpecified ≡ false

    ellipticityOrParabolicityClassSpecified :
      Bool

    ellipticityOrParabolicityClassSpecifiedIsFalse :
      ellipticityOrParabolicityClassSpecified ≡ false

    carlemanHypothesesSpecified :
      Bool

    carlemanHypothesesSpecifiedIsFalse :
      carlemanHypothesesSpecified ≡ false

    intakeImported :
      Bool

    intakeImportedIsFalse :
      intakeImported ≡ false

open CrossTermNullityAnalyticIntakeBoundary public

canonicalCrossTermNullityAnalyticIntakeBoundary :
  CrossTermNullityAnalyticIntakeBoundary
canonicalCrossTermNullityAnalyticIntakeBoundary =
  record
    { approximateCompatibilityRouteText =
        "approximate compatibility is the only recorded upstream route into the exact UCT.1-UCT.3 intake contract"
    ; approximateCompatibilityRouteTextIsCanonical =
        refl
    ; uct1ResidualPDESpecification =
        mkUnificationCrossTermIntakeClauseBoundary
          UCT1-residualPDESpecification
    ; uct1ResidualPDESpecificationIsCanonical =
        refl
    ; uct2EllipticityOrParabolicityClass =
        mkUnificationCrossTermIntakeClauseBoundary
          UCT2-ellipticityOrParabolicityClass
    ; uct2EllipticityOrParabolicityClassIsCanonical =
        refl
    ; uct3CarlemanUniqueContinuationIntake =
        mkUnificationCrossTermIntakeClauseBoundary
          UCT3-CarlemanUniqueContinuationIntake
    ; uct3CarlemanUniqueContinuationIntakeIsCanonical =
        refl
    ; uct4CrossTermNullityTheoremTarget =
        mkUnificationCrossTermIntakeClauseBoundary
          UCT4-crossTermNullityTheoremTarget
    ; uct4CrossTermNullityTheoremTargetIsCanonical =
        refl
    ; exactIntakeContractText =
        "UCT.1 exact residual PDE for c(s1,s2) -> UCT.2 elliptic/parabolic operator class -> UCT.3 Carleman/unique-continuation intake -> UCT.4 cross-term nullity theorem target"
    ; exactIntakeContractTextIsCanonical =
        refl
    ; downstreamRouteText =
        "once UCT.4 is supplied, only the fail-closed downstream chain UCT.5 modulo-null -> UCT.6 four-point -> UCT.7 parallelogram -> UCT.8 Jordan-von Neumann may read it"
    ; downstreamRouteTextIsCanonical =
        refl
    ; approximateCompatibilityRecorded =
        true
    ; approximateCompatibilityRecordedIsTrue =
        refl
    ; residualPDERecorded =
        true
    ; residualPDERecordedIsTrue =
        refl
    ; ellipticityOrParabolicityClassRecorded =
        true
    ; ellipticityOrParabolicityClassRecordedIsTrue =
        refl
    ; carlemanIntakeRecorded =
        true
    ; carlemanIntakeRecordedIsTrue =
        refl
    ; theoremTargetRecorded =
        true
    ; theoremTargetRecordedIsTrue =
        refl
    ; moduloNullConsumerHandoffRecorded =
        true
    ; moduloNullConsumerHandoffRecordedIsTrue =
        refl
    ; residualPDEHypothesesSpecified =
        false
    ; residualPDEHypothesesSpecifiedIsFalse =
        refl
    ; ellipticityOrParabolicityClassSpecified =
        false
    ; ellipticityOrParabolicityClassSpecifiedIsFalse =
        refl
    ; carlemanHypothesesSpecified =
        false
    ; carlemanHypothesesSpecifiedIsFalse =
        refl
    ; intakeImported =
        false
    ; intakeImportedIsFalse =
        refl
    }

record CrossTermNullityTheoremImportedSupport : Setω where
  field
    analyticIntakeBoundary :
      CrossTermNullityAnalyticIntakeBoundary

    discriminantBoundary :
      Discriminant.UnificationCrossTermNullityDiscriminantBoundary

    crossTermNullClassBoundary :
      CrossTerm.UnificationGluingCrossTermNullClassBoundary

    nullClassStabilityBoundary :
      NullStability.UnificationNullClassStabilityBoundary

    nullToQuotientTransportBoundary :
      NullTransport.UnificationNullToQuotientEqualityTransportBoundary

    moduloNullLinearityCompositeBoundary :
      ModuloNull.UnificationGluingModuloNullLinearityCompositeBoundary

    discriminantTheoremStillOpen :
      Discriminant.UnificationCrossTermNullityDiscriminantProved ≡ false

    crossTermExpressionRecorded :
      CrossTerm.crossTermExpressionRecorded crossTermNullClassBoundary
      ≡ true

    crossTermRepresentativeInvarianceStillOpen :
      CrossTerm.representativeInvarianceProved crossTermNullClassBoundary
      ≡ false

    crossTermNullStabilityStillOpen :
      CrossTerm.nullClassStabilityProved crossTermNullClassBoundary
      ≡ false

    parentCrossTermNullityStillOpen :
      CrossTerm.crossTermNullClassTheoremProved crossTermNullClassBoundary
      ≡ false

    stabilityRepresentativeInvarianceStillOpen :
      NullStability.representativeInvarianceProved
        nullClassStabilityBoundary
        ≡ false

    stabilityGluingStillOpen :
      NullStability.gluingOperatorStabilityProved
        nullClassStabilityBoundary
        ≡ false

    stabilityNullToQuotientStillOpen :
      NullStability.nullPredicateToQuotientEqualityTransportProved
        nullClassStabilityBoundary
        ≡ false

    transportNullToZeroStillOpen :
      NullTransport.nullToZeroBridgeProved
        nullToQuotientTransportBoundary
        ≡ false

    transportRepresentativeInvarianceStillOpen :
      NullTransport.representativeInvarianceProved
        nullToQuotientTransportBoundary
        ≡ false

    transportCrossTermToModuloLinearityStillOpen :
      NullTransport.crossTermNullToModuloLinearityProved
        nullToQuotientTransportBoundary
        ≡ false

    moduloRepresentativeInvarianceStillOpen :
      ModuloNull.representativeInvarianceProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloCrossTermNullTransportStillOpen :
      ModuloNull.crossTermNullTransportProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloQuotientEqualityStillOpen :
      ModuloNull.quotientEqualityProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloNullGluingLinearityStillOpen :
      ModuloNull.moduloNullGluingLinearityProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloFourPointConsumerStillOpen :
      ModuloNull.actualFourPointCancellationProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloParallelogramStillOpen :
      ModuloNull.parallelogramProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloQuadraticStillBlocked :
      ModuloNull.quadraticEmergenceProved
        moduloNullLinearityCompositeBoundary
        ≡ false

    moduloTerminalPromotionFalse :
      ModuloNull.terminalUnificationPromotion
        moduloNullLinearityCompositeBoundary
        ≡ false

    residualPDEHypothesesStillUnspecified :
      residualPDEHypothesesSpecified analyticIntakeBoundary ≡ false

    ellipticityOrParabolicityClassStillUnspecified :
      ellipticityOrParabolicityClassSpecified analyticIntakeBoundary ≡ false

    carlemanHypothesesStillUnspecified :
      carlemanHypothesesSpecified analyticIntakeBoundary ≡ false

    analyticIntakeStillUnimported :
      intakeImported analyticIntakeBoundary ≡ false

open CrossTermNullityTheoremImportedSupport public

canonicalCrossTermNullityTheoremImportedSupport :
  CrossTermNullityTheoremImportedSupport
canonicalCrossTermNullityTheoremImportedSupport =
  record
    { analyticIntakeBoundary =
        canonicalCrossTermNullityAnalyticIntakeBoundary
    ; discriminantBoundary =
        Discriminant.canonicalUnificationCrossTermNullityDiscriminantBoundary
    ; crossTermNullClassBoundary =
        CrossTerm.canonicalUnificationGluingCrossTermNullClassBoundary
    ; nullClassStabilityBoundary =
        NullStability.canonicalUnificationNullClassStabilityBoundary
    ; nullToQuotientTransportBoundary =
        NullTransport.canonicalUnificationNullToQuotientEqualityTransportBoundary
    ; moduloNullLinearityCompositeBoundary =
        ModuloNull.canonicalUnificationGluingModuloNullLinearityCompositeBoundary
    ; discriminantTheoremStillOpen =
        Discriminant.UnificationCrossTermNullityDiscriminantBoundary.theoremStillFalse
          Discriminant.canonicalUnificationCrossTermNullityDiscriminantBoundary
    ; crossTermExpressionRecorded =
        CrossTerm.canonicalCrossTermExpressionRecorded
    ; crossTermRepresentativeInvarianceStillOpen =
        CrossTerm.canonicalCrossTermRepresentativeInvarianceStillOpen
    ; crossTermNullStabilityStillOpen =
        CrossTerm.canonicalCrossTermNullClassStabilityStillOpen
    ; parentCrossTermNullityStillOpen =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; stabilityRepresentativeInvarianceStillOpen =
        NullStability.canonicalNullClassRepresentativeInvarianceStillOpen
    ; stabilityGluingStillOpen =
        NullStability.canonicalNullClassGluingStabilityStillOpen
    ; stabilityNullToQuotientStillOpen =
        NullStability.canonicalNullClassTransportToQuotientEqualityStillOpen
    ; transportNullToZeroStillOpen =
        NullTransport.canonicalNullToZeroBridgeStillFalse
    ; transportRepresentativeInvarianceStillOpen =
        NullTransport.canonicalRepresentativeInvarianceStillFalse
    ; transportCrossTermToModuloLinearityStillOpen =
        NullTransport.canonicalCrossTermNullToModuloLinearityStillFalse
    ; moduloRepresentativeInvarianceStillOpen =
        ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen
    ; moduloCrossTermNullTransportStillOpen =
        ModuloNull.canonicalModuloNullCrossTermNullTransportStillOpen
    ; moduloQuotientEqualityStillOpen =
        ModuloNull.canonicalModuloNullQuotientEqualityStillOpen
    ; moduloNullGluingLinearityStillOpen =
        ModuloNull.canonicalModuloNullGluingLinearityStillOpen
    ; moduloFourPointConsumerStillOpen =
        ModuloNull.canonicalModuloNullActualFourPointCancellationStillOpen
    ; moduloParallelogramStillOpen =
        ModuloNull.canonicalModuloNullParallelogramStillOpen
    ; moduloQuadraticStillBlocked =
        ModuloNull.canonicalModuloNullQuadraticStillBlocked
    ; moduloTerminalPromotionFalse =
        ModuloNull.canonicalModuloNullTerminalPromotionFalse
    ; residualPDEHypothesesStillUnspecified =
        refl
    ; ellipticityOrParabolicityClassStillUnspecified =
        refl
    ; carlemanHypothesesStillUnspecified =
        refl
    ; analyticIntakeStillUnimported =
        refl
    }

------------------------------------------------------------------------
-- Target rows.

data CrossTermNullityTheoremStage : Set where
  approximateCompatibilityRouteRecorded :
    CrossTermNullityTheoremStage

  uct1ResidualPDESpecificationRecorded :
    CrossTermNullityTheoremStage

  uct2EllipticityOrParabolicityClassRecorded :
    CrossTermNullityTheoremStage

  uct3CarlemanUniqueContinuationRecorded :
    CrossTermNullityTheoremStage

  discriminantBoundaryImported :
    CrossTermNullityTheoremStage

  parentCrossTermBoundaryImported :
    CrossTermNullityTheoremStage

  nullStabilityBoundaryImported :
    CrossTermNullityTheoremStage

  nullTransportBoundaryImported :
    CrossTermNullityTheoremStage

  moduloNullCompositeImported :
    CrossTermNullityTheoremStage

  uct4ActualTheoremTargetRecorded :
    CrossTermNullityTheoremStage

  representativeInvarianceConsumer :
    CrossTermNullityTheoremStage

  nullStabilityConsumer :
    CrossTermNullityTheoremStage

  quotientTransportConsumer :
    CrossTermNullityTheoremStage

  moduloNullLinearityConsumer :
    CrossTermNullityTheoremStage

  fourPointConsumer :
    CrossTermNullityTheoremStage

  parallelogramConsumer :
    CrossTermNullityTheoremStage

  jordanVonNeumannAdapterConsumer :
    CrossTermNullityTheoremStage

  terminalPromotionGate :
    CrossTermNullityTheoremStage

data CrossTermNullityTheoremStatus : Set where
  importedBoundary :
    CrossTermNullityTheoremStatus

  targetRecorded :
    CrossTermNullityTheoremStatus

  prerequisiteOpen :
    CrossTermNullityTheoremStatus

  theoremOpen :
    CrossTermNullityTheoremStatus

  downstreamBlocked :
    CrossTermNullityTheoremStatus

  promotionHeld :
    CrossTermNullityTheoremStatus

canonicalCrossTermNullityTheoremStatus :
  CrossTermNullityTheoremStage → CrossTermNullityTheoremStatus
canonicalCrossTermNullityTheoremStatus approximateCompatibilityRouteRecorded =
  targetRecorded
canonicalCrossTermNullityTheoremStatus uct1ResidualPDESpecificationRecorded =
  prerequisiteOpen
canonicalCrossTermNullityTheoremStatus
  uct2EllipticityOrParabolicityClassRecorded =
  prerequisiteOpen
canonicalCrossTermNullityTheoremStatus
  uct3CarlemanUniqueContinuationRecorded =
  prerequisiteOpen
canonicalCrossTermNullityTheoremStatus discriminantBoundaryImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus parentCrossTermBoundaryImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus nullStabilityBoundaryImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus nullTransportBoundaryImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus moduloNullCompositeImported =
  importedBoundary
canonicalCrossTermNullityTheoremStatus uct4ActualTheoremTargetRecorded =
  targetRecorded
canonicalCrossTermNullityTheoremStatus representativeInvarianceConsumer =
  prerequisiteOpen
canonicalCrossTermNullityTheoremStatus nullStabilityConsumer =
  prerequisiteOpen
canonicalCrossTermNullityTheoremStatus quotientTransportConsumer =
  theoremOpen
canonicalCrossTermNullityTheoremStatus moduloNullLinearityConsumer =
  downstreamBlocked
canonicalCrossTermNullityTheoremStatus fourPointConsumer =
  downstreamBlocked
canonicalCrossTermNullityTheoremStatus parallelogramConsumer =
  downstreamBlocked
canonicalCrossTermNullityTheoremStatus jordanVonNeumannAdapterConsumer =
  downstreamBlocked
canonicalCrossTermNullityTheoremStatus terminalPromotionGate =
  promotionHeld

data CrossTermNullityTheoremBlocker : Set where
  noBlockerForImportedBoundary :
    CrossTermNullityTheoremBlocker

  noBlockerForRecordedTarget :
    CrossTermNullityTheoremBlocker

  missingRepresentativeInvariance :
    CrossTermNullityTheoremBlocker

  missingNullClassStability :
    CrossTermNullityTheoremBlocker

  missingNullToQuotientTransport :
    CrossTermNullityTheoremBlocker

  missingUCT1ResidualPDESpecification :
    CrossTermNullityTheoremBlocker

  missingUCT2EllipticOrParabolicClass :
    CrossTermNullityTheoremBlocker

  missingUCT3CarlemanUniqueContinuationIntake :
    CrossTermNullityTheoremBlocker

  missingUCT4CrossTermNullityTheorem :
    CrossTermNullityTheoremBlocker

  missingModuloNullLinearityConsumer :
    CrossTermNullityTheoremBlocker

  missingFourPointConsumer :
    CrossTermNullityTheoremBlocker

  missingParallelogramConsumer :
    CrossTermNullityTheoremBlocker

  missingJordanVonNeumannAdapterConsumer :
    CrossTermNullityTheoremBlocker

  noTerminalPromotionAuthority :
    CrossTermNullityTheoremBlocker

canonicalCrossTermNullityTheoremBlocker :
  CrossTermNullityTheoremStage → CrossTermNullityTheoremBlocker
canonicalCrossTermNullityTheoremBlocker approximateCompatibilityRouteRecorded =
  noBlockerForRecordedTarget
canonicalCrossTermNullityTheoremBlocker uct1ResidualPDESpecificationRecorded =
  missingUCT1ResidualPDESpecification
canonicalCrossTermNullityTheoremBlocker
  uct2EllipticityOrParabolicityClassRecorded =
  missingUCT2EllipticOrParabolicClass
canonicalCrossTermNullityTheoremBlocker
  uct3CarlemanUniqueContinuationRecorded =
  missingUCT3CarlemanUniqueContinuationIntake
canonicalCrossTermNullityTheoremBlocker discriminantBoundaryImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker parentCrossTermBoundaryImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker nullStabilityBoundaryImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker nullTransportBoundaryImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker moduloNullCompositeImported =
  noBlockerForImportedBoundary
canonicalCrossTermNullityTheoremBlocker uct4ActualTheoremTargetRecorded =
  noBlockerForRecordedTarget
canonicalCrossTermNullityTheoremBlocker representativeInvarianceConsumer =
  missingRepresentativeInvariance
canonicalCrossTermNullityTheoremBlocker nullStabilityConsumer =
  missingNullClassStability
canonicalCrossTermNullityTheoremBlocker quotientTransportConsumer =
  missingUCT4CrossTermNullityTheorem
canonicalCrossTermNullityTheoremBlocker moduloNullLinearityConsumer =
  missingModuloNullLinearityConsumer
canonicalCrossTermNullityTheoremBlocker fourPointConsumer =
  missingFourPointConsumer
canonicalCrossTermNullityTheoremBlocker parallelogramConsumer =
  missingParallelogramConsumer
canonicalCrossTermNullityTheoremBlocker jordanVonNeumannAdapterConsumer =
  missingJordanVonNeumannAdapterConsumer
canonicalCrossTermNullityTheoremBlocker terminalPromotionGate =
  noTerminalPromotionAuthority

record CrossTermNullityTheoremRow : Set where
  field
    stage :
      CrossTermNullityTheoremStage

    status :
      CrossTermNullityTheoremStatus

    statusIsCanonical :
      status ≡ canonicalCrossTermNullityTheoremStatus stage

    blocker :
      CrossTermNullityTheoremBlocker

    blockerIsCanonical :
      blocker ≡ canonicalCrossTermNullityTheoremBlocker stage

    targetOrConsumer :
      String

    importedSurface :
      String

    provedOrPromotedHere :
      Bool

    provedOrPromotedHereIsFalse :
      provedOrPromotedHere ≡ false

open CrossTermNullityTheoremRow public

mkCrossTermNullityTheoremRow :
  CrossTermNullityTheoremStage →
  String →
  String →
  CrossTermNullityTheoremRow
mkCrossTermNullityTheoremRow stage targetOrConsumer importedSurface =
  record
    { stage =
        stage
    ; status =
        canonicalCrossTermNullityTheoremStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalCrossTermNullityTheoremBlocker stage
    ; blockerIsCanonical =
        refl
    ; targetOrConsumer =
        targetOrConsumer
    ; importedSurface =
        importedSurface
    ; provedOrPromotedHere =
        false
    ; provedOrPromotedHereIsFalse =
        refl
    }

canonicalCrossTermNullityTheoremRows :
  List CrossTermNullityTheoremRow
canonicalCrossTermNullityTheoremRows =
  mkCrossTermNullityTheoremRow
    approximateCompatibilityRouteRecorded
    "record the candidate route approximate compatibility -> UCT.1 exact residual PDE for c(s1,s2) -> UCT.2 operator class -> UCT.3 Carleman intake"
    "CrossTermNullityAnalyticIntakeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    uct1ResidualPDESpecificationRecorded
    "UCT.1 specifies the exact residual PDE carried by c(s1,s2)=G(s1 +V s2) -V G(s1) -V G(s2)"
    "CrossTermNullityAnalyticIntakeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    uct2EllipticityOrParabolicityClassRecorded
    "UCT.2 fixes whether the UCT.1 residual PDE sits in the elliptic or parabolic regime"
    "CrossTermNullityAnalyticIntakeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    uct3CarlemanUniqueContinuationRecorded
    "UCT.3 records the exact Carleman/unique-continuation intake compatible with UCT.2 and sufficient for UCT.4"
    "CrossTermNullityAnalyticIntakeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    discriminantBoundaryImported
    "consume discriminant/Cauchy-Schwarz seed only as upstream evidence for the UCT-gated cross-term nullity theorem"
    "UnificationCrossTermNullityDiscriminantBoundary"
  ∷ mkCrossTermNullityTheoremRow
    parentCrossTermBoundaryImported
    "consume recorded expression G(s1+s2)-G(s1)-G(s2)"
    "UnificationGluingCrossTermNullClassBoundary"
  ∷ mkCrossTermNullityTheoremRow
    nullStabilityBoundaryImported
    "consume null-class operation and G-stability blockers"
    "UnificationNullClassStabilityBoundary"
  ∷ mkCrossTermNullityTheoremRow
    nullTransportBoundaryImported
    "consume null predicate to quotient equality transport blockers"
    "UnificationNullToQuotientEqualityTransportBoundary"
  ∷ mkCrossTermNullityTheoremRow
    moduloNullCompositeImported
    "consume representative invariance, cross-term transport, quotient equality, and modulo-null route"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    uct4ActualTheoremTargetRecorded
    "UCT.4 target: forall s1 s2, nullClass (c(s1,s2)) where c(s1,s2)=G(s1 +V s2) -V G(s1) -V G(s2)"
    "U1aCrossTermNullityTheoremTarget"
  ∷ mkCrossTermNullityTheoremRow
    representativeInvarianceConsumer
    "representatives must not change cross-term nullity"
    "NullStability, NullTransport, ModuloNull"
  ∷ mkCrossTermNullityTheoremRow
    nullStabilityConsumer
    "null class must be stable under quotient operations and G"
    "UnificationNullClassStabilityBoundary"
  ∷ mkCrossTermNullityTheoremRow
    quotientTransportConsumer
    "once UCT.4 is imported, the theorem must identify the cross-term with the null class strongly enough to transport to quotient equality with zero"
    "UnificationNullToQuotientEqualityTransportBoundary"
  ∷ mkCrossTermNullityTheoremRow
    moduloNullLinearityConsumer
    "UCT.5 consumes UCT.4 only through fail-closed null-to-quotient transport into modulo-null gluing linearity"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    fourPointConsumer
    "UCT.6 consumes UCT.5 only through fail-closed four-point cancellation on the modulo-null side"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    parallelogramConsumer
    "UCT.7 consumes UCT.6 only through fail-closed parallelogram data"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkCrossTermNullityTheoremRow
    jordanVonNeumannAdapterConsumer
    "UCT.8 consumes UCT.7 only through fail-closed Jordan-von Neumann adapter surfaces on V/null"
    "UnificationJordanVonNeumannAdapterBoundary"
  ∷ mkCrossTermNullityTheoremRow
    terminalPromotionGate
    "terminal unification promotion remains held"
    "all imported promotion gates"
  ∷ []

canonicalCrossTermNullityTheoremRowCount : Nat
canonicalCrossTermNullityTheoremRowCount =
  listLength canonicalCrossTermNullityTheoremRows

canonicalCrossTermNullityTheoremRowCountIs13 :
  canonicalCrossTermNullityTheoremRowCount ≡ 18
canonicalCrossTermNullityTheoremRowCountIs13 =
  refl

------------------------------------------------------------------------
-- Boundary.

data CrossTermNullityTerminalPromotionAuthority : Set where

crossTermNullityTerminalPromotionAuthorityImpossible :
  CrossTermNullityTerminalPromotionAuthority →
  ⊥
crossTermNullityTerminalPromotionAuthorityImpossible ()

record UnificationCrossTermNullityTheoremBoundary : Setω where
  field
    importedSupport :
      CrossTermNullityTheoremImportedSupport

    exactGrammarBoundary :
      CrossTermNullityExactGrammarBoundary

    theoremRows :
      List CrossTermNullityTheoremRow

    theoremRowCount :
      Nat

    theoremRowCountIs13 :
      theoremRowCount ≡ 18

    theoremRowCountMatchesRows :
      theoremRowCount ≡ listLength theoremRows

    actualTheoremTargetRecorded :
      Bool

    actualTheoremTargetRecordedIsTrue :
      actualTheoremTargetRecorded ≡ true

    theoremTargetText :
      String

    theoremTargetTextIsCanonical :
      theoremTargetText
      ≡ "forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2))"

    candidateTheoremGrammarText :
      String

    candidateTheoremGrammarTextIsCanonical :
      candidateTheoremGrammarText
      ≡ "UCT.1 exact residual PDE for c(s1,s2) -> UCT.2 elliptic/parabolic operator class -> UCT.3 Carleman/unique-continuation intake -> UCT.4 forall s1 s2, nullClass (c(s1,s2)) -> UCT.5 modulo-null -> UCT.6 four-point -> UCT.7 parallelogram -> UCT.8 Jordan-von Neumann on V/null"

    downstreamConsumerChainText :
      String

    downstreamConsumerChainTextIsCanonical :
      downstreamConsumerChainText
      ≡ "explicit downstream chain: UCT.4 cross-term nullity -> UCT.5 modulo-null consumer -> UCT.6 four-point consumer -> UCT.7 parallelogram consumer -> UCT.8 Jordan-von Neumann consumer"

    representativeInvarianceRecorded :
      Bool

    representativeInvarianceRecordedIsTrue :
      representativeInvarianceRecorded ≡ true

    nullStabilityRecorded :
      Bool

    nullStabilityRecordedIsTrue :
      nullStabilityRecorded ≡ true

    quotientTransportRecorded :
      Bool

    quotientTransportRecordedIsTrue :
      quotientTransportRecorded ≡ true

    moduloNullLinearityConsumerRecorded :
      Bool

    moduloNullLinearityConsumerRecordedIsTrue :
      moduloNullLinearityConsumerRecorded ≡ true

    fourPointConsumerRecorded :
      Bool

    fourPointConsumerRecordedIsTrue :
      fourPointConsumerRecorded ≡ true

    parallelogramConsumerRecorded :
      Bool

    parallelogramConsumerRecordedIsTrue :
      parallelogramConsumerRecorded ≡ true

    jordanVonNeumannAdapterConsumerRecorded :
      Bool

    jordanVonNeumannAdapterConsumerRecordedIsTrue :
      jordanVonNeumannAdapterConsumerRecorded ≡ true

    analyticIntakeRecorded :
      Bool

    analyticIntakeRecordedIsTrue :
      analyticIntakeRecorded ≡ true

    ellipticityOrParabolicityClassRecorded :
      Bool

    ellipticityOrParabolicityClassRecordedIsTrue :
      ellipticityOrParabolicityClassRecorded ≡ true

    residualPDEHypothesesSpecified :
      Bool

    residualPDEHypothesesSpecifiedIsFalse :
      residualPDEHypothesesSpecified ≡ false

    ellipticityOrParabolicityClassSpecified :
      Bool

    ellipticityOrParabolicityClassSpecifiedIsFalse :
      ellipticityOrParabolicityClassSpecified ≡ false

    carlemanHypothesesSpecified :
      Bool

    carlemanHypothesesSpecifiedIsFalse :
      carlemanHypothesesSpecified ≡ false

    analyticIntakeImported :
      Bool

    analyticIntakeImportedIsFalse :
      analyticIntakeImported ≡ false

    representativeInvarianceProved :
      Bool

    representativeInvarianceProvedIsFalse :
      representativeInvarianceProved ≡ false

    nullStabilityProved :
      Bool

    nullStabilityProvedIsFalse :
      nullStabilityProved ≡ false

    quotientTransportProved :
      Bool

    quotientTransportProvedIsFalse :
      quotientTransportProved ≡ false

    crossTermNullityTheoremProved :
      Bool

    crossTermNullityTheoremProvedIsFalse :
      crossTermNullityTheoremProved ≡ false

    moduloNullLinearityProved :
      Bool

    moduloNullLinearityProvedIsFalse :
      moduloNullLinearityProved ≡ false

    fourPointConsumerProved :
      Bool

    fourPointConsumerProvedIsFalse :
      fourPointConsumerProved ≡ false

    parallelogramProved :
      Bool

    parallelogramProvedIsFalse :
      parallelogramProved ≡ false

    jordanVonNeumannAdapterProved :
      Bool

    jordanVonNeumannAdapterProvedIsFalse :
      jordanVonNeumannAdapterProved ≡ false

    quadraticEmergenceProved :
      Bool

    quadraticEmergenceProvedIsFalse :
      quadraticEmergenceProved ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    allTheoremFourPointParallelogramQuadraticTerminalFlagsFalse :
      Bool

    allTheoremFourPointParallelogramQuadraticTerminalFlagsFalseIsTrue :
      allTheoremFourPointParallelogramQuadraticTerminalFlagsFalse ≡ true

    promotionAuthorityImpossible :
      CrossTermNullityTerminalPromotionAuthority →
      ⊥

    notes :
      List String

open UnificationCrossTermNullityTheoremBoundary public

canonicalUnificationCrossTermNullityTheoremBoundary :
  UnificationCrossTermNullityTheoremBoundary
canonicalUnificationCrossTermNullityTheoremBoundary =
  record
    { importedSupport =
        canonicalCrossTermNullityTheoremImportedSupport
    ; exactGrammarBoundary =
        canonicalCrossTermNullityExactGrammarBoundary
    ; theoremRows =
        canonicalCrossTermNullityTheoremRows
    ; theoremRowCount =
        18
    ; theoremRowCountIs13 =
        refl
    ; theoremRowCountMatchesRows =
        refl
    ; actualTheoremTargetRecorded =
        true
    ; actualTheoremTargetRecordedIsTrue =
        refl
    ; theoremTargetText =
        "forall s1 s2, nullClass (G(s1 +V s2) -V G(s1) -V G(s2))"
    ; theoremTargetTextIsCanonical =
        refl
    ; candidateTheoremGrammarText =
        "UCT.1 exact residual PDE for c(s1,s2) -> UCT.2 elliptic/parabolic operator class -> UCT.3 Carleman/unique-continuation intake -> UCT.4 forall s1 s2, nullClass (c(s1,s2)) -> UCT.5 modulo-null -> UCT.6 four-point -> UCT.7 parallelogram -> UCT.8 Jordan-von Neumann on V/null"
    ; candidateTheoremGrammarTextIsCanonical =
        refl
    ; downstreamConsumerChainText =
        "explicit downstream chain: UCT.4 cross-term nullity -> UCT.5 modulo-null consumer -> UCT.6 four-point consumer -> UCT.7 parallelogram consumer -> UCT.8 Jordan-von Neumann consumer"
    ; downstreamConsumerChainTextIsCanonical =
        refl
    ; representativeInvarianceRecorded =
        true
    ; representativeInvarianceRecordedIsTrue =
        refl
    ; nullStabilityRecorded =
        true
    ; nullStabilityRecordedIsTrue =
        refl
    ; quotientTransportRecorded =
        true
    ; quotientTransportRecordedIsTrue =
        refl
    ; moduloNullLinearityConsumerRecorded =
        true
    ; moduloNullLinearityConsumerRecordedIsTrue =
        refl
    ; fourPointConsumerRecorded =
        true
    ; fourPointConsumerRecordedIsTrue =
        refl
    ; parallelogramConsumerRecorded =
        true
    ; parallelogramConsumerRecordedIsTrue =
        refl
    ; jordanVonNeumannAdapterConsumerRecorded =
        true
    ; jordanVonNeumannAdapterConsumerRecordedIsTrue =
        refl
    ; analyticIntakeRecorded =
        true
    ; analyticIntakeRecordedIsTrue =
        refl
    ; ellipticityOrParabolicityClassRecorded =
        true
    ; ellipticityOrParabolicityClassRecordedIsTrue =
        refl
    ; residualPDEHypothesesSpecified =
        false
    ; residualPDEHypothesesSpecifiedIsFalse =
        refl
    ; ellipticityOrParabolicityClassSpecified =
        false
    ; ellipticityOrParabolicityClassSpecifiedIsFalse =
        refl
    ; carlemanHypothesesSpecified =
        false
    ; carlemanHypothesesSpecifiedIsFalse =
        refl
    ; analyticIntakeImported =
        false
    ; analyticIntakeImportedIsFalse =
        refl
    ; representativeInvarianceProved =
        false
    ; representativeInvarianceProvedIsFalse =
        ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen
    ; nullStabilityProved =
        false
    ; nullStabilityProvedIsFalse =
        CrossTerm.canonicalCrossTermNullClassStabilityStillOpen
    ; quotientTransportProved =
        false
    ; quotientTransportProvedIsFalse =
        NullTransport.canonicalNullToZeroBridgeStillFalse
    ; crossTermNullityTheoremProved =
        false
    ; crossTermNullityTheoremProvedIsFalse =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; moduloNullLinearityProved =
        false
    ; moduloNullLinearityProvedIsFalse =
        ModuloNull.canonicalModuloNullGluingLinearityStillOpen
    ; fourPointConsumerProved =
        false
    ; fourPointConsumerProvedIsFalse =
        ModuloNull.canonicalModuloNullActualFourPointCancellationStillOpen
    ; parallelogramProved =
        false
    ; parallelogramProvedIsFalse =
        ModuloNull.canonicalModuloNullParallelogramStillOpen
    ; jordanVonNeumannAdapterProved =
        false
    ; jordanVonNeumannAdapterProvedIsFalse =
        refl
    ; quadraticEmergenceProved =
        false
    ; quadraticEmergenceProvedIsFalse =
        ModuloNull.canonicalModuloNullQuadraticStillBlocked
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        ModuloNull.canonicalModuloNullTerminalPromotionFalse
    ; allTheoremFourPointParallelogramQuadraticTerminalFlagsFalse =
        true
    ; allTheoremFourPointParallelogramQuadraticTerminalFlagsFalseIsTrue =
        refl
    ; promotionAuthorityImpossible =
        crossTermNullityTerminalPromotionAuthorityImpossible
    ; notes =
        "Live frontier: approximate compatibility is recorded only as the upstream route into the exact UCT.1-UCT.3 intake contract."
      ∷ "UCT.1 records the missing residual PDE specification for c(s1,s2)=G(s1 +V s2) -V G(s1) -V G(s2)."
      ∷ "UCT.2 records the missing elliptic/parabolic class that fixes the unique-continuation regime for UCT.1."
      ∷ "UCT.3 records the missing Carleman/unique-continuation intake matched to UCT.2 and strong enough to force UCT.4."
      ∷ "UCT.4 records the single theorem-sized target forall s1 s2, nullClass (c(s1,s2))."
      ∷ "UCT.5 records the fail-closed modulo-null consumer reached only through null-to-quotient transport."
      ∷ "UCT.6 records the fail-closed four-point cancellation consumer on the modulo-null side."
      ∷ "UCT.7 records the fail-closed parallelogram consumer."
      ∷ "UCT.8 records the fail-closed Jordan-von Neumann adapter consumer on V/null."
      ∷ "The discriminant surface is consumed only as an upstream seed and does not itself prove cross-term nullity."
      ∷ "Representative invariance, null stability, quotient transport, and modulo-null linearity are consumed from existing fail-closed boundaries."
      ∷ "Modulo-null linearity, four-point, parallelogram, Jordan-von Neumann recovery, quadratic emergence, and terminal promotion remain downstream consumers only."
      ∷ "Theorem, four-point, parallelogram, Jordan-von Neumann, quadratic, and terminal promotion flags remain false."
      ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas for downstream consumers.

canonicalCrossTermNullityTheoremRowsCountIs13 :
  theoremRowCount canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ 18
canonicalCrossTermNullityTheoremRowsCountIs13 =
  refl

canonicalCrossTermNullityActualTargetRecorded :
  actualTheoremTargetRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityActualTargetRecorded =
  refl

canonicalCrossTermNullityRepresentativeInvarianceRecorded :
  representativeInvarianceRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityRepresentativeInvarianceRecorded =
  refl

canonicalCrossTermNullityNullStabilityRecorded :
  nullStabilityRecorded canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityNullStabilityRecorded =
  refl

canonicalCrossTermNullityQuotientTransportRecorded :
  quotientTransportRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityQuotientTransportRecorded =
  refl

canonicalCrossTermNullityModuloNullLinearityConsumerRecorded :
  moduloNullLinearityConsumerRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityModuloNullLinearityConsumerRecorded =
  refl

canonicalCrossTermNullityFourPointConsumerRecorded :
  fourPointConsumerRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityFourPointConsumerRecorded =
  refl

canonicalCrossTermNullityParallelogramConsumerRecorded :
  parallelogramConsumerRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityParallelogramConsumerRecorded =
  refl

canonicalCrossTermNullityJordanVonNeumannAdapterConsumerRecorded :
  jordanVonNeumannAdapterConsumerRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityJordanVonNeumannAdapterConsumerRecorded =
  refl

canonicalCrossTermNullityAnalyticIntakeRecorded :
  analyticIntakeRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityAnalyticIntakeRecorded =
  refl

canonicalCrossTermNullityResidualPDEHypothesesStillUnspecified :
  residualPDEHypothesesSpecified
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityResidualPDEHypothesesStillUnspecified =
  refl

canonicalCrossTermNullityEllipticityOrParabolicityClassRecorded :
  ellipticityOrParabolicityClassRecorded
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityEllipticityOrParabolicityClassRecorded =
  refl

canonicalCrossTermNullityEllipticityOrParabolicityClassStillUnspecified :
  ellipticityOrParabolicityClassSpecified
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityEllipticityOrParabolicityClassStillUnspecified =
  refl

canonicalCrossTermNullityCarlemanHypothesesStillUnspecified :
  carlemanHypothesesSpecified
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityCarlemanHypothesesStillUnspecified =
  refl

canonicalCrossTermNullityAnalyticIntakeStillUnimported :
  analyticIntakeImported
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityAnalyticIntakeStillUnimported =
  refl

canonicalCrossTermNullityRepresentativeInvarianceStillOpen :
  representativeInvarianceProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityRepresentativeInvarianceStillOpen =
  ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen

canonicalCrossTermNullityNullStabilityStillOpen :
  nullStabilityProved canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityNullStabilityStillOpen =
  CrossTerm.canonicalCrossTermNullClassStabilityStillOpen

canonicalCrossTermNullityQuotientTransportStillOpen :
  quotientTransportProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityQuotientTransportStillOpen =
  NullTransport.canonicalNullToZeroBridgeStillFalse

canonicalCrossTermNullityTheoremStillOpen :
  crossTermNullityTheoremProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityTheoremStillOpen =
  CrossTerm.canonicalCrossTermNullClassTheoremStillOpen

canonicalCrossTermNullityModuloNullLinearityStillOpen :
  moduloNullLinearityProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityModuloNullLinearityStillOpen =
  ModuloNull.canonicalModuloNullGluingLinearityStillOpen

canonicalCrossTermNullityFourPointConsumerStillOpen :
  fourPointConsumerProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityFourPointConsumerStillOpen =
  ModuloNull.canonicalModuloNullActualFourPointCancellationStillOpen

canonicalCrossTermNullityParallelogramStillOpen :
  parallelogramProved canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityParallelogramStillOpen =
  ModuloNull.canonicalModuloNullParallelogramStillOpen

canonicalCrossTermNullityJordanVonNeumannStillOpen :
  jordanVonNeumannAdapterProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityJordanVonNeumannStillOpen =
  refl

canonicalCrossTermNullityQuadraticStillBlocked :
  quadraticEmergenceProved
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityQuadraticStillBlocked =
  ModuloNull.canonicalModuloNullQuadraticStillBlocked

canonicalCrossTermNullityTerminalPromotionFalse :
  terminalPromotion canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ false
canonicalCrossTermNullityTerminalPromotionFalse =
  ModuloNull.canonicalModuloNullTerminalPromotionFalse

canonicalCrossTermNullityTheoremPromotionBundleFalse :
  allTheoremFourPointParallelogramQuadraticTerminalFlagsFalse
    canonicalUnificationCrossTermNullityTheoremBoundary
  ≡ true
canonicalCrossTermNullityTheoremPromotionBundleFalse =
  refl
