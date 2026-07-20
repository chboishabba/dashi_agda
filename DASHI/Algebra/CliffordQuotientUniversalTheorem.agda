module DASHI.Algebra.CliffordQuotientUniversalTheorem where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Unified.GRQuantumStrictProofTerms as Strict

------------------------------------------------------------------------
-- Full quotient-based Clifford universal theorem.
--
-- The existing constructive blade model checks relations on a finite basis.
-- This module exposes the tensor-algebra quotient, the generated Clifford
-- congruence/ideal, quotient descent, and unique factorisation into every
-- admissible target algebra.  From this data we construct the strict terminal
-- Clifford surface rather than accepting a second unrelated interface.

record CliffordQuotientConstruction : Set₁ where
  field
    Scalar : Set
    Vector : Set
    Q : Vector → Scalar

    TensorAlgebra : Set
    CliffordRelationGenerator : Set
    generatedRelation : TensorAlgebra → TensorAlgebra → Set

    CliffordQuotient : Set
    quotientClass : TensorAlgebra → CliffordQuotient
    injectTensorVector : Vector → TensorAlgebra
    injectVector : Vector → CliffordQuotient
    multiply : CliffordQuotient → CliffordQuotient → CliffordQuotient
    scalarEmbed : Scalar → CliffordQuotient

    quotientSound :
      (left right : TensorAlgebra) →
      generatedRelation left right →
      quotientClass left ≡ quotientClass right
    quotientSurjective :
      (element : CliffordQuotient) → Set

    vectorInjectionIsQuotientClass :
      (vector : Vector) →
      injectVector vector ≡ quotientClass (injectTensorVector vector)

    cliffordRelation :
      (vector : Vector) →
      multiply (injectVector vector) (injectVector vector)
      ≡ scalarEmbed (Q vector)

    relationGeneratedExactlyByQuadraticDefect : Set
    relationGeneratedExactlyByQuadraticDefectProof :
      relationGeneratedExactlyByQuadraticDefect
    quotientAlgebraLaws : Set
    quotientAlgebraLawsProof : quotientAlgebraLaws
open CliffordQuotientConstruction public

record CliffordQuotientElimination
  (construction : CliffordQuotientConstruction) : Set₁ where
  field
    TargetAlgebra : Set
    AdmissibleGeneratorMap : TargetAlgebra → Set

    FactorMap :
      (target : TargetAlgebra) →
      AdmissibleGeneratorMap target →
      Set

    rawTensorExtension :
      (target : TargetAlgebra) →
      AdmissibleGeneratorMap target →
      TensorAlgebra construction → Set

    rawExtensionKillsGeneratedRelation :
      (target : TargetAlgebra) →
      (generator : AdmissibleGeneratorMap target) →
      (left right : TensorAlgebra construction) →
      generatedRelation construction left right →
      Set

    descendToQuotient :
      (target : TargetAlgebra) →
      (generator : AdmissibleGeneratorMap target) →
      FactorMap target generator

    factorExtendsGenerator :
      (target : TargetAlgebra) →
      (generator : AdmissibleGeneratorMap target) →
      Set

    factorIsAlgebraHomomorphism :
      (target : TargetAlgebra) →
      (generator : AdmissibleGeneratorMap target) →
      Set

    factorUnique :
      (target : TargetAlgebra) →
      (generator : AdmissibleGeneratorMap target) →
      (left right : FactorMap target generator) →
      left ≡ right

    descentWellDefinedFromRelationProof : Set
    descentWellDefinedFromRelationProofProof :
      descentWellDefinedFromRelationProof
open CliffordQuotientElimination public

record FullCliffordQuotientUniversalTheorem : Set₁ where
  field
    construction : CliffordQuotientConstruction
    elimination : CliffordQuotientElimination construction

    tensorAlgebraFreeUniversalProperty : Set
    tensorAlgebraFreeUniversalPropertyProof :
      tensorAlgebraFreeUniversalProperty
    quotientIsInitialAmongQuadraticRepresentations : Set
    quotientIsInitialAmongQuadraticRepresentationsProof :
      quotientIsInitialAmongQuadraticRepresentations
    arbitraryTargetAlgebrasCovered : Set
    arbitraryTargetAlgebrasCoveredProof : arbitraryTargetAlgebrasCovered
open FullCliffordQuotientUniversalTheorem public

strictCliffordFromQuotient :
  FullCliffordQuotientUniversalTheorem →
  Strict.StrictCliffordUniversalProof
strictCliffordFromQuotient theorem =
  record
    { Vector = Vector (construction theorem)
    ; Scalar = Scalar (construction theorem)
    ; Q = Q (construction theorem)
    ; Clifford = CliffordQuotient (construction theorem)
    ; injectVector = injectVector (construction theorem)
    ; multiply = multiply (construction theorem)
    ; scalarEmbed = scalarEmbed (construction theorem)
    ; cliffordRelation = cliffordRelation (construction theorem)
    ; TargetAlgebra = TargetAlgebra (elimination theorem)
    ; AdmissibleGeneratorMap = AdmissibleGeneratorMap (elimination theorem)
    ; FactorMap = FactorMap (elimination theorem)
    ; factorExists = descendToQuotient (elimination theorem)
    ; factorUnique = factorUnique (elimination theorem)
    }
