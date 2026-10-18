module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedSelfApplicationExact where

------------------------------------------------------------------------
-- CANDIDATE-CODE SELF-APPLICATION THROUGH LITERAL PROGRAM QUOTATION
--
-- The remaining A1 representation seam is a quotation map
--
--   finite Program -> Cook.BooleanFormula.
--
-- Given ANY such quotation, this owner builds a finite primitive whose binary
-- semantics really consumes its quoted program:
--
--   runCandidateOnQuote q
--      = runCandidateCode c_D (quoteProgram q).
--
-- Applying the repository's existing literal finite specialization/diagonal
-- construction to that primitive yields an actual fixed program p*_D with
--
--   run1 p*_D tt
--      = just (decide D (quoteProgram p*_D)).
--
-- This is genuine candidate-aware self-application.  It contains no SAT
-- correctness, satisfiability, opposite-polarity, or decision-failure premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (_≤_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≢_; trans)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width

------------------------------------------------------------------------
-- Quotation interface.
--
-- No semantic law is hidden here: it is only finite syntax -> Cook syntax.
-- A later concrete implementation can quote constructor tags and embedded
-- candidate-code bits using the repository's existing finite bit/formula
-- encoders.
------------------------------------------------------------------------

record ProgramFormulaQuotation (Primitive : Set) : Set₁ where
  field
    quoteProgram :
      Code.Program Primitive →
      Cook.BooleanFormula

open ProgramFormulaQuotation public

------------------------------------------------------------------------
-- One primitive: evaluate D on the literal quotation of the quoted program.
------------------------------------------------------------------------

data CandidateQuotedPrimitive
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set where
  runCandidateOnQuote :
    CandidateQuotedPrimitive code

------------------------------------------------------------------------
-- Candidate-aware binary semantics.
------------------------------------------------------------------------

candidateQuotedPrimitiveSemantics :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)) →
  Code.PrimitiveSemantics
    (CandidateQuotedPrimitive code)
    ⊤
    Bool
candidateQuotedPrimitiveSemantics code quotation =
  record
    { Code.runPrimitive1 =
        λ primitive input → nothing
    ; Code.runPrimitive2 =
        λ primitive quoted input →
          just
            (Actual.CandidateCodeRealization.runCandidateCode
              code
              (Actual.CandidateCodeRealization.candidateCode code)
              (quoteProgram quotation quoted))
    }

candidateQuotedPrimitiveRunsExactDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code))
    (quoted :
      Code.Program
        (CandidateQuotedPrimitive code)) →
  Code.runPrimitive2
      (candidateQuotedPrimitiveSemantics code quotation)
      runCandidateOnQuote
      quoted
      tt
  ≡
  just
    (Direct.decide
      candidate
      (quoteProgram quotation quoted))
candidateQuotedPrimitiveRunsExactDecision
    code
    quotation
    quoted
    rewrite
      Actual.CandidateCodeRealization.codeDecisionExact
        code
        (quoteProgram quotation quoted) =
  refl

------------------------------------------------------------------------
-- Literal fixed point from the repository's finite code calculus.
------------------------------------------------------------------------

candidateQuotedFixedPointProgram :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  Code.Program
    (CandidateQuotedPrimitive code)
candidateQuotedFixedPointProgram code =
  Code.primitiveBodyFixedPoint
    runCandidateOnQuote

candidateQuotedFixedPointFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  ProgramFormulaQuotation
    (CandidateQuotedPrimitive code) →
  Cook.BooleanFormula
candidateQuotedFixedPointFormula code quotation =
  quoteProgram quotation
    (candidateQuotedFixedPointProgram code)

------------------------------------------------------------------------
-- Exact operational self-application theorem.
------------------------------------------------------------------------

candidateQuotedFixedPointRunsCandidateOnOwnQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)) →
  Code.run1
      (candidateQuotedPrimitiveSemantics code quotation)
      (candidateQuotedFixedPointProgram code)
      tt
  ≡
  just
    (Direct.decide
      candidate
      (candidateQuotedFixedPointFormula
        code
        quotation))
candidateQuotedFixedPointRunsCandidateOnOwnQuotation
    code
    quotation =
  trans
    (Code.primitiveBodyFixedPointRun
      (candidateQuotedPrimitiveSemantics code quotation)
      runCandidateOnQuote
      tt)
    (candidateQuotedPrimitiveRunsExactDecision
      code
      quotation
      (candidateQuotedFixedPointProgram code))

------------------------------------------------------------------------
-- Same-object operational root package.
--
-- The Boolean root is literally the quotation of the actual self-specialized
-- finite program whose execution invokes D on that same quotation.
------------------------------------------------------------------------

record CandidateQuotedSelfApplication
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (code : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)

    fixedProgram :
      Code.Program
        (CandidateQuotedPrimitive code)

    fixedProgramExact :
      fixedProgram
      ≡
      candidateQuotedFixedPointProgram code

    rootFormula :
      Cook.BooleanFormula

    rootFormulaExact :
      rootFormula
      ≡
      quoteProgram quotation fixedProgram

    executionExact :
      Code.run1
        (candidateQuotedPrimitiveSemantics
          code quotation)
        fixedProgram
        tt
      ≡
      just
        (Direct.decide candidate rootFormula)

open CandidateQuotedSelfApplication public

canonicalCandidateQuotedSelfApplication :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)) →
  CandidateQuotedSelfApplication candidate code
canonicalCandidateQuotedSelfApplication
    {candidate = candidate}
    code
    quotation =
  record
    { quotation =
        quotation
    ; fixedProgram =
        candidateQuotedFixedPointProgram code
    ; fixedProgramExact =
        refl
    ; rootFormula =
        candidateQuotedFixedPointFormula code quotation
    ; rootFormulaExact =
        refl
    ; executionExact =
        candidateQuotedFixedPointRunsCandidateOnOwnQuotation
          code quotation
    }

------------------------------------------------------------------------
-- Structural quotation from candidate-code quotation.
--
-- CandidateCode remains abstract at this layer, so the only representation
-- input required is a literal Cook-formula quotation of that exact code.
-- Program constructor tags are then encoded structurally with ordinary Cook
-- syntax.  No SAT meaning is assigned to the quotation.
------------------------------------------------------------------------

record CandidateCodeFormulaQuotation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    quoteCandidateCode :
      Actual.CandidateCodeRealization.CandidateCode code →
      Cook.BooleanFormula

open CandidateCodeFormulaQuotation public

structuralProgramQuote :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  CandidateCodeFormulaQuotation code →
  Code.Program (CandidateQuotedPrimitive code) →
  Cook.BooleanFormula
structuralProgramQuote
    codeQuotation
    (Code.primitive runCandidateOnQuote) =
  Cook.conjunction
    (quoteCandidateCode
      codeQuotation
      (Actual.CandidateCodeRealization.candidateCode code))
    (Cook.constant true)
structuralProgramQuote
    codeQuotation
    (Code.specialized program static) =
  Cook.conjunction
    (Cook.disjunction
      (Cook.constant true)
      (Cook.constant false))
    (Cook.conjunction
      (structuralProgramQuote codeQuotation program)
      (structuralProgramQuote codeQuotation static))
structuralProgramQuote
    codeQuotation
    (Code.diagonalized program) =
  Cook.conjunction
    (Cook.negate (Cook.constant false))
    (structuralProgramQuote codeQuotation program)

structuralProgramFormulaQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  CandidateCodeFormulaQuotation code →
  ProgramFormulaQuotation
    (CandidateQuotedPrimitive code)
structuralProgramFormulaQuotation codeQuotation =
  record
    { quoteProgram =
        structuralProgramQuote codeQuotation
    }

------------------------------------------------------------------------
-- Literal Q2 state for the operational self-application root.
--
-- currentFormula is definitionally the quotation of the actual candidate-aware
-- fixed program.  Persistent code size is the exact c_D size; rebinding is the
-- literal finite Program syntax size.  The budget is chosen equal to the exact
-- represented-state measure, so fit is reflexive rather than assumed.
------------------------------------------------------------------------

candidateQuotedSelfApplicationState :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codeQuotation : CandidateCodeFormulaQuotation code) →
  Q2.BoundedSelfReferenceState
candidateQuotedSelfApplicationState code codeQuotation =
  Q2.bounded-self-reference-state
    root
    codeSize
    rebinding
    (Size.formulaNodeCount root + (codeSize + rebinding))
    NatP.≤-refl
  where
    quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)
    quotation =
      structuralProgramFormulaQuotation codeQuotation

    root :
      Cook.BooleanFormula
    root =
      candidateQuotedFixedPointFormula
        code
        quotation

    codeSize :
      Nat
    codeSize =
      Actual.CandidateCodeRealization.codeSize
        code
        (Actual.CandidateCodeRealization.candidateCode code)

    rebinding :
      Nat
    rebinding =
      Code.programSize
        (candidateQuotedFixedPointProgram code)

candidateQuotedStateCurrentFormulaExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codeQuotation : CandidateCodeFormulaQuotation code) →
  Q2.currentFormula
    (candidateQuotedSelfApplicationState code codeQuotation)
  ≡
  candidateQuotedFixedPointFormula
    code
    (structuralProgramFormulaQuotation codeQuotation)
candidateQuotedStateCurrentFormulaExact code codeQuotation =
  refl

candidateQuotedStateProgramCodeSizeExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codeQuotation : CandidateCodeFormulaQuotation code) →
  Q2.programCodeSize
    (candidateQuotedSelfApplicationState code codeQuotation)
  ≡
  Actual.CandidateCodeRealization.codeSize
    code
    (Actual.CandidateCodeRealization.candidateCode code)
candidateQuotedStateProgramCodeSizeExact code codeQuotation =
  refl

candidateQuotedStateRebindingExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codeQuotation : CandidateCodeFormulaQuotation code) →
  Q2.rebindingOverhead
    (candidateQuotedSelfApplicationState code codeQuotation)
  ≡
  Code.programSize
    (candidateQuotedFixedPointProgram code)
candidateQuotedStateRebindingExact code codeQuotation =
  refl

candidateQuotedStateBudgetExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codeQuotation : CandidateCodeFormulaQuotation code) →
  Q2.resourceBudget
    (candidateQuotedSelfApplicationState code codeQuotation)
  ≡
  Q2.recursiveMeasure
    (candidateQuotedSelfApplicationState code codeQuotation)
candidateQuotedStateBudgetExact code codeQuotation =
  refl

candidateQuotedStateRunsCandidateOnCurrentFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codeQuotation : CandidateCodeFormulaQuotation code) →
  Code.run1
      (candidateQuotedPrimitiveSemantics
        code
        (structuralProgramFormulaQuotation codeQuotation))
      (candidateQuotedFixedPointProgram code)
      tt
  ≡
  just
    (Direct.decide
      candidate
      (Q2.currentFormula
        (candidateQuotedSelfApplicationState
          code
          codeQuotation)))
candidateQuotedStateRunsCandidateOnCurrentFormula
    code
    codeQuotation =
  candidateQuotedFixedPointRunsCandidateOnOwnQuotation
    code
    (structuralProgramFormulaQuotation codeQuotation)

------------------------------------------------------------------------
-- Faithful candidate-code quotation.
--
-- A bare quotation function may erase its input.  The faithful surface adds a
-- left inverse, exactly as the concrete-tape static-program codecs elsewhere
-- in the repository do.  This is representation adequacy only.
------------------------------------------------------------------------

record FaithfulCandidateCodeFormulaQuotation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    quotation :
      CandidateCodeFormulaQuotation code

    decodeCandidateCode :
      Cook.BooleanFormula →
      Actual.CandidateCodeRealization.CandidateCode code

    decodeQuoteCandidateCode :
      (candidateCode :
        Actual.CandidateCodeRealization.CandidateCode code) →
      decodeCandidateCode
        (quoteCandidateCode quotation candidateCode)
      ≡
      candidateCode

open FaithfulCandidateCodeFormulaQuotation public

faithfulCandidateQuotedSelfApplicationState :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  FaithfulCandidateCodeFormulaQuotation code →
  Q2.BoundedSelfReferenceState
faithfulCandidateQuotedSelfApplicationState code faithful =
  candidateQuotedSelfApplicationState
    code
    (quotation faithful)

------------------------------------------------------------------------
-- B on the exact A1 root.
------------------------------------------------------------------------

CandidateQuotedFirstStepProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  FaithfulCandidateCodeFormulaQuotation code →
  DirectDP.DirectDPChargedStateConstructor →
  Set
CandidateQuotedFirstStepProgress
    code
    faithful
    constructor =
  constructor
    (faithfulCandidateQuotedSelfApplicationState
      code faithful)
  ≢
  nothing

------------------------------------------------------------------------
-- C attacks that same root directly.
------------------------------------------------------------------------

candidateQuotedHighWidthForcesStop :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (faithful : FaithfulCandidateCodeFormulaQuotation code)
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula
          (faithfulCandidateQuotedSelfApplicationState
            code faithful))}
    remaining
    width →
  Q2.recursiveMeasure
      (faithfulCandidateQuotedSelfApplicationState
        code faithful)
  ≤
  Width.triple width →
  constructor
      (faithfulCandidateQuotedSelfApplicationState
        code faithful)
  ≡
  nothing
candidateQuotedHighWidthForcesStop
    code
    faithful
    constructor
    witness
    measureBelowWidth =
  DirectDP.directDPHighWidthForcesConstructorStop
    witness
    measureBelowWidth
    constructor

candidateQuotedWidthRefutesProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (faithful : FaithfulCandidateCodeFormulaQuotation code)
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula
          (faithfulCandidateQuotedSelfApplicationState
            code faithful))}
    remaining
    width →
  Q2.recursiveMeasure
      (faithfulCandidateQuotedSelfApplicationState
        code faithful)
  ≤
  Width.triple width →
  CandidateQuotedFirstStepProgress
    code
    faithful
    constructor →
  ⊥
candidateQuotedWidthRefutesProgress
    code
    faithful
    constructor
    witness
    measureBelowWidth
    progress =
  progress
    (candidateQuotedHighWidthForcesStop
      code
      faithful
      constructor
      witness
      measureBelowWidth)

------------------------------------------------------------------------
-- Strength firewall.
--
-- This package proves only:
--
--   p*_D evaluates D on quote(p*_D).
--
-- It DOES NOT prove:
--
--   SAT(quote(p*_D)) iff D rejects quote(p*_D),
--   quote(p*_D) = oppositeResponse(D, quote(p*_D)),
--   constructor(s_D) != nothing.
--
-- Therefore this operational same-object self-application is strictly below
-- the already-proved SAT-failure-strength semantic response self-equation.
------------------------------------------------------------------------

data CandidateQuotedSelfApplicationStatus : Set where
  candidateCodeConsumed : CandidateQuotedSelfApplicationStatus
  quotedProgramConsumed : CandidateQuotedSelfApplicationStatus
  literalFiniteFixedPointPaid : CandidateQuotedSelfApplicationStatus
  ownQuotationDecisionExact : CandidateQuotedSelfApplicationStatus
  satPolaritySemanticsPaid : CandidateQuotedSelfApplicationStatus
  firstStepProgressPaid : CandidateQuotedSelfApplicationStatus

currentCandidateQuotedSelfApplicationStatus :
  CandidateQuotedSelfApplicationStatus
currentCandidateQuotedSelfApplicationStatus =
  ownQuotationDecisionExact

------------------------------------------------------------------------
-- FRONTIER
--
-- A1 is now reduced to a representation theorem:
--
--   implement ProgramFormulaQuotation concretely,
--   bind rootFormula to Q2.currentFormula(s_D),
--   charge candidate-code + quotation/rebinding size exactly.
--
-- The candidate-aware self-application computation itself is paid.
--
-- Only after that exact Q2 root exists should B ask whether the direct-DP
-- constructor must make one successful step.
------------------------------------------------------------------------
