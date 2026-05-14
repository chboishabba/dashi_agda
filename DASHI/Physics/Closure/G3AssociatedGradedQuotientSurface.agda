module DASHI.Physics.Closure.G3AssociatedGradedQuotientSurface where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _+_; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.G3PoincareGalileiCarrierChain as Chain
import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3WaveFunctionOperatorAlgebra as G3

------------------------------------------------------------------------
-- G3 associated-graded quotient surface.
--
-- Worker 1's selected associated-graded evidence identifies the selected
-- Galilei generators and their p2 degrees.  This module records the next
-- exact layer: the quotient carrier
--
--   gr(F) = direct sum_n F_n / F_{n-1}
--
-- together with the projection from selected wave-function operators into
-- the quotient.  No quotient is fabricated here: the current repo has
-- selected degree evidence, but it has no accepted equivalence relation
-- modulo the previous filtration piece and no quotient/setoid primitive for
-- this G3 operator algebra.

data G3AssociatedGradedQuotientStatus : Set where
  quotientSurfaceOnlyNoPromotion :
    G3AssociatedGradedQuotientStatus

data G3AssociatedGradedQuotientFirstMissing : Set where
  missingFiltrationSubspaceCarrier :
    G3AssociatedGradedQuotientFirstMissing

  missingPreviousFiltrationInclusion :
    G3AssociatedGradedQuotientFirstMissing

  missingEquivalenceModuloPreviousFiltration :
    G3AssociatedGradedQuotientFirstMissing

  missingAcceptedQuotientCarrier :
    G3AssociatedGradedQuotientFirstMissing

  missingProjectionRespectsQuotientEquivalence :
    G3AssociatedGradedQuotientFirstMissing

  missingP2IndexedPoincareCarrier :
    G3AssociatedGradedQuotientFirstMissing

  missingP2IndexedPoincareGalileiIsomorphism :
    G3AssociatedGradedQuotientFirstMissing

data G3AssociatedGradedProjectionStatus : Set where
  noAcceptedProjectionIntoGradedQuotient :
    G3AssociatedGradedProjectionStatus

  selectedProjectionIntoFiltrationPieceOnlyNoQuotient :
    G3AssociatedGradedProjectionStatus

data G3EquivalenceModuloPreviousFiltrationPrimitiveBlocker : Set where
  missingSelectedFiltrationOperatorDifferenceClosure :
    G3EquivalenceModuloPreviousFiltrationPrimitiveBlocker

  missingSelectedPreviousFiltrationZeroDifference :
    G3EquivalenceModuloPreviousFiltrationPrimitiveBlocker

  missingSelectedPreviousFiltrationNegationClosure :
    G3EquivalenceModuloPreviousFiltrationPrimitiveBlocker

  missingSelectedPreviousFiltrationAdditionClosure :
    G3EquivalenceModuloPreviousFiltrationPrimitiveBlocker

  missingSelectedPreviousFiltrationDifferenceImageMembership :
    G3EquivalenceModuloPreviousFiltrationPrimitiveBlocker

  missingAcceptedOperatorEqualityOrSetoidForDifferenceImage :
    G3EquivalenceModuloPreviousFiltrationPrimitiveBlocker

------------------------------------------------------------------------
-- Concrete selected prequotient layer.
--
-- The selected operator algebra does give a real filtration carrier:
-- an operator paired with its selected p2-degree evidence.  This is the
-- F_n side of gr_n(F) = F_n / F_{n-1}.  What is still absent is the
-- previous-filtration inclusion/equivalence/quotient primitive needed to
-- turn these pieces into quotient classes.

SelectedFiltrationPiece :
  Nat →
  Set
SelectedFiltrationPiece n =
  Σ G3.WaveFunctionOperator
    (λ A → G3.SelectedOperatorP2Degree A n)

selectedFiltrationOperator :
  (n : Nat) →
  SelectedFiltrationPiece n →
  G3.WaveFunctionOperator
selectedFiltrationOperator n piece =
  proj₁ piece

selectedFiltrationDegreeEvidence :
  (n : Nat) →
  (piece : SelectedFiltrationPiece n) →
  G3.SelectedOperatorP2Degree
    (selectedFiltrationOperator n piece)
    n
selectedFiltrationDegreeEvidence n piece =
  proj₂ piece

selectedProjectionToFiltrationPiece :
  (n : Nat) →
  (A : G3.WaveFunctionOperator) →
  G3.SelectedOperatorP2Degree A n →
  SelectedFiltrationPiece n
selectedProjectionToFiltrationPiece n A deg =
  A , deg

selectedGeneratorFiltrationPiece :
  (g : G3.G3SelectedAssociatedGradedGenerator) →
  SelectedFiltrationPiece (G3.selectedGeneratorDegree g)
selectedGeneratorFiltrationPiece g =
  selectedProjectionToFiltrationPiece
    (G3.selectedGeneratorDegree g)
    (G3.selectedGeneratorOperator g)
    (G3.selectedGeneratorHasDegree g)

selectedBracketFiltrationPiece :
  {A B : G3.WaveFunctionOperator} →
  {m n : Nat} →
  G3.SelectedOperatorP2Degree A m →
  G3.SelectedOperatorP2Degree B n →
  SelectedFiltrationPiece (m + n)
selectedBracketFiltrationPiece {A} {B} {m} {n} degA degB =
  selectedProjectionToFiltrationPiece
    (m + n)
    (G3.operatorCommutator A B)
    (G3.selectedBracketRespectsP2Degree degA degB)

------------------------------------------------------------------------
-- Selected cumulative filtration and previous-in-current inclusion.
--
-- SelectedOperatorP2Degree is an exact-degree witness.  There is no
-- honest local weakening rule turning degree n into degree suc n.  The
-- standard filtration carrier is therefore the cumulative wrapper
-- F<= n = Σ k . k <= n × F_exact k.  With that carrier, previous
-- filtration inclusion is real and constructive:
--
--   F<= n -> F<= suc n

≤-sucʳ :
  {m n : Nat} →
  m ≤ n →
  m ≤ suc n
≤-sucʳ z≤n =
  z≤n
≤-sucʳ (s≤s m≤n) =
  s≤s (≤-sucʳ m≤n)

≤-refl :
  (n : Nat) →
  n ≤ n
≤-refl zero =
  z≤n
≤-refl (suc n) =
  s≤s (≤-refl n)

SelectedCumulativeFiltrationPiece :
  Nat →
  Set
SelectedCumulativeFiltrationPiece n =
  Σ Nat
    (λ k → Σ (k ≤ n)
      (λ _ → SelectedFiltrationPiece k))

selectedCumulativeFiltrationOperator :
  (n : Nat) →
  SelectedCumulativeFiltrationPiece n →
  G3.WaveFunctionOperator
selectedCumulativeFiltrationOperator n piece =
  selectedFiltrationOperator
    (proj₁ piece)
    (proj₂ (proj₂ piece))

selectedExactToCumulativeFiltrationPiece :
  (n : Nat) →
  SelectedFiltrationPiece n →
  SelectedCumulativeFiltrationPiece n
selectedExactToCumulativeFiltrationPiece n piece =
  n , ≤-refl n , piece

selectedPreviousIncludedInCurrent :
  (n : Nat) →
  SelectedCumulativeFiltrationPiece n →
  SelectedCumulativeFiltrationPiece (suc n)
selectedPreviousIncludedInCurrent n piece =
  proj₁ piece ,
  ≤-sucʳ (proj₁ (proj₂ piece)) ,
  proj₂ (proj₂ piece)

-- Candidate only: A and B are equivalent modulo the previous cumulative
-- filtration when their ambient operator difference is represented by a
-- selected F<= n piece.  This uses the subtraction helper exported by
-- G3WaveFunctionOperatorAlgebra, but it is not yet an accepted equivalence:
-- the selected filtration has no additive-group closure or image-membership
-- API proving reflexivity/symmetry/transitivity for this predicate.
SelectedEquivalentModuloPreviousCumulativeFiltration :
  (n : Nat) →
  G3.WaveFunctionOperator →
  G3.WaveFunctionOperator →
  Set
SelectedEquivalentModuloPreviousCumulativeFiltration n A B =
  Σ (SelectedCumulativeFiltrationPiece n)
    (λ previousPiece →
      selectedCumulativeFiltrationOperator n previousPiece
      ≡
      G3.waveFunctionOperatorSubtraction A B)

record G3SelectedOperatorPointwiseEqualitySurface : Setω where
  field
    operatorEquality :
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator →
      Set

    operatorEqualityIsPointwise :
      operatorEquality ≡ G3.WaveFunctionOperatorPointwiseEquality

    operatorEqualityRefl :
      (A : G3.WaveFunctionOperator) →
      operatorEquality A A

    operatorEqualitySym :
      (A B : G3.WaveFunctionOperator) →
      operatorEquality A B →
      operatorEquality B A

    operatorEqualityTrans :
      (A B C : G3.WaveFunctionOperator) →
      operatorEquality A B →
      operatorEquality B C →
      operatorEquality A C

    zeroDifferencePointwise :
      (A : G3.WaveFunctionOperator) →
      operatorEquality
        (G3.waveFunctionOperatorSubtraction A A)
        G3.zeroWaveFunctionOperator

    negatedDifferencePointwise :
      (A B : G3.WaveFunctionOperator) →
      operatorEquality
        (G3.waveFunctionOperatorSubtraction B A)
        (G3.waveFunctionOperatorNegation
          (G3.waveFunctionOperatorSubtraction A B))

    additiveDifferencePointwise :
      (A B C : G3.WaveFunctionOperator) →
      operatorEquality
        (G3.waveFunctionOperatorAddition
          (G3.waveFunctionOperatorSubtraction A B)
          (G3.waveFunctionOperatorSubtraction B C))
        (G3.waveFunctionOperatorSubtraction A C)

    equalitySurfaceBoundary :
      List String

canonicalG3SelectedOperatorPointwiseEqualitySurface :
  G3SelectedOperatorPointwiseEqualitySurface
canonicalG3SelectedOperatorPointwiseEqualitySurface =
  record
    { operatorEquality =
        G3.WaveFunctionOperatorPointwiseEquality
    ; operatorEqualityIsPointwise =
        refl
    ; operatorEqualityRefl =
        G3.waveFunctionOperatorPointwiseRefl
    ; operatorEqualitySym =
        G3.waveFunctionOperatorPointwiseSym
    ; operatorEqualityTrans =
        G3.waveFunctionOperatorPointwiseTrans
    ; zeroDifferencePointwise =
        G3.waveFunctionOperatorZeroDifferencePointwise
    ; negatedDifferencePointwise =
        G3.waveFunctionOperatorNegatedDifferencePointwise
    ; additiveDifferencePointwise =
        G3.waveFunctionOperatorAdditiveDifferencePointwise
    ; equalitySurfaceBoundary =
        "Accepted local operator equality is pointwise equality on wave-function operators"
        ∷ "Zero difference, negated difference, and additive difference laws are now typechecked pointwise laws from the G3 operator definitions"
        ∷ "These laws do not by themselves prove that zero/difference/additive witnesses are represented inside the selected previous cumulative filtration"
        ∷ []
    }

record G3SelectedOperatorSetoidSurface : Setω where
  field
    equalitySurface :
      G3SelectedOperatorPointwiseEqualitySurface

    Carrier :
      Set

    CarrierIsWaveFunctionOperator :
      Carrier ≡ G3.WaveFunctionOperator

    _≈_ :
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator →
      Set

    equalityIsPointwise :
      _≈_ ≡
      G3SelectedOperatorPointwiseEqualitySurface.operatorEquality
        equalitySurface

    refl≈ :
      (A : G3.WaveFunctionOperator) →
      A ≈ A

    sym≈ :
      (A B : G3.WaveFunctionOperator) →
      A ≈ B →
      B ≈ A

    trans≈ :
      (A B C : G3.WaveFunctionOperator) →
      A ≈ B →
      B ≈ C →
      A ≈ C

    setoidBoundary :
      List String

canonicalG3SelectedOperatorSetoidSurface :
  G3SelectedOperatorSetoidSurface
canonicalG3SelectedOperatorSetoidSurface =
  record
    { equalitySurface =
        canonicalG3SelectedOperatorPointwiseEqualitySurface
    ; Carrier =
        G3.WaveFunctionOperator
    ; CarrierIsWaveFunctionOperator =
        refl
    ; _≈_ =
        G3.WaveFunctionOperatorPointwiseEquality
    ; equalityIsPointwise =
        refl
    ; refl≈ =
        G3.waveFunctionOperatorPointwiseRefl
    ; sym≈ =
        G3.waveFunctionOperatorPointwiseSym
    ; trans≈ =
        G3.waveFunctionOperatorPointwiseTrans
    ; setoidBoundary =
        "Local operator setoid surface is pointwise equality on G3.WaveFunctionOperator"
        ∷ "This is an equality surface only; it does not manufacture previous-filtration representatives"
        ∷ []
    }

record G3SelectedOperatorAdditiveQuotientPrimitive : Setω where
  field
    equalitySurface :
      G3SelectedOperatorPointwiseEqualitySurface

    operatorZero :
      G3.WaveFunctionOperator

    operatorZeroIsG3Zero :
      operatorZero ≡ G3.zeroWaveFunctionOperator

    operatorAddition :
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator

    operatorAdditionIsG3Addition :
      operatorAddition ≡ G3.waveFunctionOperatorAddition

    operatorNegation :
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator

    operatorNegationIsG3Negation :
      operatorNegation ≡ G3.waveFunctionOperatorNegation

    operatorDifference :
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator

    operatorDifferenceIsG3Subtraction :
      operatorDifference ≡ G3.waveFunctionOperatorSubtraction

    zeroDifferenceInPreviousFiltration :
      (n : Nat) →
      (A : G3.WaveFunctionOperator) →
      SelectedEquivalentModuloPreviousCumulativeFiltration n A A

    negationClosureInPreviousFiltration :
      (n : Nat) →
      (A B : G3.WaveFunctionOperator) →
      SelectedEquivalentModuloPreviousCumulativeFiltration n A B →
      SelectedEquivalentModuloPreviousCumulativeFiltration n B A

    additionClosureInPreviousFiltration :
      (n : Nat) →
      (A B C : G3.WaveFunctionOperator) →
      SelectedEquivalentModuloPreviousCumulativeFiltration n A B →
      SelectedEquivalentModuloPreviousCumulativeFiltration n B C →
      SelectedEquivalentModuloPreviousCumulativeFiltration n A C

    acceptedDifferenceImageMembership :
      (n : Nat) →
      (A B : G3.WaveFunctionOperator) →
      SelectedEquivalentModuloPreviousCumulativeFiltration n A B →
      Σ (SelectedCumulativeFiltrationPiece n)
        (λ previousPiece →
          G3SelectedOperatorPointwiseEqualitySurface.operatorEquality
            equalitySurface
            (selectedCumulativeFiltrationOperator n previousPiece)
            (operatorDifference A B))

    additiveQuotientPrimitiveBoundary :
      List String

record G3SelectedModuloPreviousEquivalenceOnPrimitive
  (prim : G3SelectedOperatorAdditiveQuotientPrimitive) : Setω where
  field
    relation :
      (n : Nat) →
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator →
      Set

    relationIsSelectedCandidate :
      relation ≡ SelectedEquivalentModuloPreviousCumulativeFiltration

    reflModuloPrevious :
      (n : Nat) →
      (A : G3.WaveFunctionOperator) →
      relation n A A

    symModuloPrevious :
      (n : Nat) →
      (A B : G3.WaveFunctionOperator) →
      relation n A B →
      relation n B A

    transModuloPrevious :
      (n : Nat) →
      (A B C : G3.WaveFunctionOperator) →
      relation n A B →
      relation n B C →
      relation n A C

    acceptedDifferenceMembership :
      (n : Nat) →
      (A B : G3.WaveFunctionOperator) →
      relation n A B →
      Σ (SelectedCumulativeFiltrationPiece n)
        (λ previousPiece →
          G3SelectedOperatorPointwiseEqualitySurface.operatorEquality
            (G3SelectedOperatorAdditiveQuotientPrimitive.equalitySurface prim)
            (selectedCumulativeFiltrationOperator n previousPiece)
            (G3SelectedOperatorAdditiveQuotientPrimitive.operatorDifference prim A B))

    primitiveEquivalenceBoundary :
      List String

selectedModuloPreviousEquivalenceFromPrimitive :
  (prim : G3SelectedOperatorAdditiveQuotientPrimitive) →
  G3SelectedModuloPreviousEquivalenceOnPrimitive prim
selectedModuloPreviousEquivalenceFromPrimitive prim =
  record
    { relation =
        SelectedEquivalentModuloPreviousCumulativeFiltration
    ; relationIsSelectedCandidate =
        refl
    ; reflModuloPrevious =
        G3SelectedOperatorAdditiveQuotientPrimitive.zeroDifferenceInPreviousFiltration
          prim
    ; symModuloPrevious =
        G3SelectedOperatorAdditiveQuotientPrimitive.negationClosureInPreviousFiltration
          prim
    ; transModuloPrevious =
        G3SelectedOperatorAdditiveQuotientPrimitive.additionClosureInPreviousFiltration
          prim
    ; acceptedDifferenceMembership =
        G3SelectedOperatorAdditiveQuotientPrimitive.acceptedDifferenceImageMembership
          prim
    ; primitiveEquivalenceBoundary =
        "If the additive quotient primitive is inhabited, the selected candidate relation is reflexive, symmetric, and transitive"
        ∷ "The proof consumes only zero-difference, negation closure, addition closure, and accepted difference-image membership fields"
        ∷ "No primitive is constructed here; this is a typed receipt schema for the first missing gate"
        ∷ []
    }

record G3SelectedEquivalenceModuloPreviousFiltrationBlocker : Setω where
  field
    operatorSetoidSurface :
      G3SelectedOperatorSetoidSurface

    pointwiseOperatorEqualitySurface :
      G3SelectedOperatorPointwiseEqualitySurface

    currentFiltrationPiece :
      Nat →
      Set

    currentFiltrationPieceIsSelected :
      currentFiltrationPiece ≡ SelectedCumulativeFiltrationPiece

    previousInCurrent :
      (n : Nat) →
      SelectedCumulativeFiltrationPiece n →
      SelectedCumulativeFiltrationPiece (suc n)

    previousInCurrentIsSelected :
      previousInCurrent ≡ selectedPreviousIncludedInCurrent

    ambientOperatorDifference :
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator

    ambientOperatorDifferenceIsG3Subtraction :
      ambientOperatorDifference ≡ G3.waveFunctionOperatorSubtraction

    candidateEquivalentModuloPrevious :
      (n : Nat) →
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator →
      Set

    candidateEquivalentModuloPreviousIsSelected :
      candidateEquivalentModuloPrevious
      ≡
      SelectedEquivalentModuloPreviousCumulativeFiltration

    missingPrimitives :
      List G3EquivalenceModuloPreviousFiltrationPrimitiveBlocker

    exactBlockerBoundary :
      List String

canonicalG3SelectedEquivalenceModuloPreviousFiltrationBlocker :
  G3SelectedEquivalenceModuloPreviousFiltrationBlocker
canonicalG3SelectedEquivalenceModuloPreviousFiltrationBlocker =
  record
    { operatorSetoidSurface =
        canonicalG3SelectedOperatorSetoidSurface
    ; pointwiseOperatorEqualitySurface =
        canonicalG3SelectedOperatorPointwiseEqualitySurface
    ; currentFiltrationPiece =
        SelectedCumulativeFiltrationPiece
    ; currentFiltrationPieceIsSelected =
        refl
    ; previousInCurrent =
        selectedPreviousIncludedInCurrent
    ; previousInCurrentIsSelected =
        refl
    ; ambientOperatorDifference =
        G3.waveFunctionOperatorSubtraction
    ; ambientOperatorDifferenceIsG3Subtraction =
        refl
    ; candidateEquivalentModuloPrevious =
        SelectedEquivalentModuloPreviousCumulativeFiltration
    ; candidateEquivalentModuloPreviousIsSelected =
        refl
    ; missingPrimitives =
        missingSelectedFiltrationOperatorDifferenceClosure
        ∷ missingSelectedPreviousFiltrationZeroDifference
        ∷ missingSelectedPreviousFiltrationNegationClosure
        ∷ missingSelectedPreviousFiltrationAdditionClosure
        ∷ missingSelectedPreviousFiltrationDifferenceImageMembership
        ∷ []
    ; exactBlockerBoundary =
        "Candidate relation: A ~ B modulo F<=n when G3.waveFunctionOperatorSubtraction A B is represented by a selected previous cumulative filtration piece"
        ∷ "The local operator setoid surface is now pointwise equality on WaveFunctionOperator"
        ∷ "The ambient operator subtraction function exists, but the selected cumulative filtration has no closure primitive for operator differences"
        ∷ "Pointwise operator equality/setoid laws are now exposed, including zero difference, negated difference, and additive difference laws"
        ∷ "Reflexivity is blocked by the absence of a selected zero-difference witness in the previous cumulative filtration"
        ∷ "Symmetry is blocked by the absence of selected previous-filtration negation closure"
        ∷ "Transitivity is blocked by the absence of selected previous-filtration addition closure for difference witnesses"
        ∷ "Projection to a quotient is blocked by the absence of an accepted image-membership API consuming pointwise equality for difference representatives"
        ∷ []
    }

record G3SelectedPreviousFiltrationInclusionEvidence : Setω where
  field
    exactFiltrationPiece :
      Nat →
      Set

    exactFiltrationPieceIsSelected :
      exactFiltrationPiece ≡ SelectedFiltrationPiece

    cumulativeFiltrationPiece :
      Nat →
      Set

    cumulativeFiltrationPieceIsSelected :
      cumulativeFiltrationPiece ≡ SelectedCumulativeFiltrationPiece

    exactToCumulative :
      (n : Nat) →
      SelectedFiltrationPiece n →
      SelectedCumulativeFiltrationPiece n

    exactToCumulativeIsSelected :
      exactToCumulative ≡ selectedExactToCumulativeFiltrationPiece

    previousIncludedInCurrent :
      (n : Nat) →
      SelectedCumulativeFiltrationPiece n →
      SelectedCumulativeFiltrationPiece (suc n)

    previousIncludedInCurrentIsSelected :
      previousIncludedInCurrent ≡ selectedPreviousIncludedInCurrent

    exactRemainingBoundary :
      List String

canonicalG3SelectedPreviousFiltrationInclusionEvidence :
  G3SelectedPreviousFiltrationInclusionEvidence
canonicalG3SelectedPreviousFiltrationInclusionEvidence =
  record
    { exactFiltrationPiece =
        SelectedFiltrationPiece
    ; exactFiltrationPieceIsSelected =
        refl
    ; cumulativeFiltrationPiece =
        SelectedCumulativeFiltrationPiece
    ; cumulativeFiltrationPieceIsSelected =
        refl
    ; exactToCumulative =
        selectedExactToCumulativeFiltrationPiece
    ; exactToCumulativeIsSelected =
        refl
    ; previousIncludedInCurrent =
        selectedPreviousIncludedInCurrent
    ; previousIncludedInCurrentIsSelected =
        refl
    ; exactRemainingBoundary =
        "Previous filtration inclusion is now constructive for the cumulative carrier F<= n = Sigma k . k <= n × F_exact k"
        ∷ "No exact-degree weakening SelectedOperatorP2Degree A n -> SelectedOperatorP2Degree A (suc n) is claimed"
        ∷ "The remaining quotient blocker is equivalence modulo the previous cumulative filtration and an accepted quotient carrier"
        ∷ []
    }

record G3SelectedAssociatedGradedPrequotientEvidence : Setω where
  field
    filtrationPiece :
      Nat →
      Set

    filtrationPieceIsSelected :
      filtrationPiece ≡ SelectedFiltrationPiece

    projectionToFiltrationPiece :
      (n : Nat) →
      (A : G3.WaveFunctionOperator) →
      G3.SelectedOperatorP2Degree A n →
      SelectedFiltrationPiece n

    projectionToFiltrationPieceIsSelected :
      projectionToFiltrationPiece
      ≡
      selectedProjectionToFiltrationPiece

    generatorProjection :
      (g : G3.G3SelectedAssociatedGradedGenerator) →
      SelectedFiltrationPiece (G3.selectedGeneratorDegree g)

    generatorProjectionIsSelected :
      generatorProjection ≡ selectedGeneratorFiltrationPiece

    spatialMomentumProjection :
      (d : G3Concrete.G3SpatialDirection) →
      SelectedFiltrationPiece
        (G3.selectedGeneratorDegree
          (G3.selectedSpatialMomentumGenerator d))

    hamiltonianProjection :
      SelectedFiltrationPiece
        (G3.selectedGeneratorDegree
          G3.selectedHamiltonianGenerator)

    boostProjection :
      (d : G3Concrete.G3SpatialDirection) →
      SelectedFiltrationPiece
        (G3.selectedGeneratorDegree
          (G3.selectedBoostGenerator d))

    massCentralProjection :
      SelectedFiltrationPiece
        (G3.selectedGeneratorDegree
          G3.selectedMassCentralSlot)

    bracketProjection :
      {A B : G3.WaveFunctionOperator} →
      {m n : Nat} →
      G3.SelectedOperatorP2Degree A m →
      G3.SelectedOperatorP2Degree B n →
      SelectedFiltrationPiece (m + n)

    bracketProjectionIsSelected :
      {A B : G3.WaveFunctionOperator} →
      {m n : Nat} →
      (degA : G3.SelectedOperatorP2Degree A m) →
      (degB : G3.SelectedOperatorP2Degree B n) →
      bracketProjection degA degB
      ≡
      selectedBracketFiltrationPiece degA degB

    exactPrequotientBoundary :
      List String

canonicalG3SelectedAssociatedGradedPrequotientEvidence :
  G3SelectedAssociatedGradedPrequotientEvidence
canonicalG3SelectedAssociatedGradedPrequotientEvidence =
  record
    { filtrationPiece =
        SelectedFiltrationPiece
    ; filtrationPieceIsSelected =
        refl
    ; projectionToFiltrationPiece =
        selectedProjectionToFiltrationPiece
    ; projectionToFiltrationPieceIsSelected =
        refl
    ; generatorProjection =
        selectedGeneratorFiltrationPiece
    ; generatorProjectionIsSelected =
        refl
    ; spatialMomentumProjection =
        λ d →
          selectedGeneratorFiltrationPiece
            (G3.selectedSpatialMomentumGenerator d)
    ; hamiltonianProjection =
        selectedGeneratorFiltrationPiece
          G3.selectedHamiltonianGenerator
    ; boostProjection =
        λ d →
          selectedGeneratorFiltrationPiece
            (G3.selectedBoostGenerator d)
    ; massCentralProjection =
        selectedGeneratorFiltrationPiece
          G3.selectedMassCentralSlot
    ; bracketProjection =
        selectedBracketFiltrationPiece
    ; bracketProjectionIsSelected =
        λ _ _ → refl
    ; exactPrequotientBoundary =
        "Concrete selected prequotient carrier F_n is now inhabited as Sigma WaveFunctionOperator (SelectedOperatorP2Degree _ n)"
        ∷ "Selected generators P/H/K/mass project into their concrete F_n pieces by selectedGeneratorHasDegree"
        ∷ "Explicit selected P, H, K, and mass-central projections are named as prequotient slots"
        ∷ "Selected brackets project into F_{m+n} by selectedBracketRespectsP2Degree"
        ∷ "No quotient class F_n / F_{n-1} is constructed: an accepted equivalence modulo previous filtration and quotient carrier are still missing"
        ∷ []
    }

-- Required API for a real gr(F) layer.  This is the normalized target
-- surface: an implementation can close this lane by providing these fields
-- against the selected operator algebra.
record G3AssociatedGradedQuotientAPI : Setω where
  field
    FiltrationPiece :
      Nat →
      Set

    PreviousFiltrationPiece :
      Nat →
      Set

    previousIncludedInCurrent :
      (n : Nat) →
      PreviousFiltrationPiece n →
      FiltrationPiece n

    operatorInFiltration :
      (n : Nat) →
      (A : G3.WaveFunctionOperator) →
      G3.SelectedOperatorP2Degree A n →
      Set

    equivalentModuloPrevious :
      (n : Nat) →
      G3.WaveFunctionOperator →
      G3.WaveFunctionOperator →
      Set

    quotientCarrier :
      Nat →
      Set

    projection :
      (n : Nat) →
      (A : G3.WaveFunctionOperator) →
      G3.SelectedOperatorP2Degree A n →
      quotientCarrier n

    projectionRespectsEquivalentModuloPrevious :
      (n : Nat) →
      (A B : G3.WaveFunctionOperator) →
      (degA : G3.SelectedOperatorP2Degree A n) →
      (degB : G3.SelectedOperatorP2Degree B n) →
      equivalentModuloPrevious n A B →
      projection n A degA ≡ projection n B degB

    bracketDescendsToQuotient :
      (m n : Nat) →
      (A B : G3.WaveFunctionOperator) →
      (degA : G3.SelectedOperatorP2Degree A m) →
      (degB : G3.SelectedOperatorP2Degree B n) →
      Set

-- The SES/G3 promotion needs one more bridge after the quotient exists:
-- a p2-indexed Poincare carrier and an isomorphism from its p2 -> infinity
-- associated graded into the selected Galilei quotient carrier.
record G3P2IndexedPoincareGalileiIsomorphismAPI
  (quotientAPI : G3AssociatedGradedQuotientAPI) : Setω where
  field
    PoincareAtP2 :
      Nat →
      Set

    poincareProjection :
      (n : Nat) →
      PoincareAtP2 n →
      G3AssociatedGradedQuotientAPI.quotientCarrier quotientAPI n

    galileiSection :
      (n : Nat) →
      G3AssociatedGradedQuotientAPI.quotientCarrier quotientAPI n →
      PoincareAtP2 n

    projectionSectionLeftInverse :
      (n : Nat) →
      (x : G3AssociatedGradedQuotientAPI.quotientCarrier quotientAPI n) →
      poincareProjection n (galileiSection n x) ≡ x

    projectionSectionRightInverse :
      (n : Nat) →
      (x : PoincareAtP2 n) →
      galileiSection n (poincareProjection n x) ≡ x

record G3AssociatedGradedQuotientSurface : Setω where
  field
    status :
      G3AssociatedGradedQuotientStatus

    selectedGeneratorEvidence :
      G3.G3SelectedAssociatedGradedGalileiEvidence

    filteredBracketCompatibility :
      G3.G3SelectedFilteredBracketCompatibility

    selectedPrequotientEvidence :
      G3SelectedAssociatedGradedPrequotientEvidence

    selectedPreviousFiltrationInclusionEvidence :
      G3SelectedPreviousFiltrationInclusionEvidence

    selectedEquivalenceModuloPreviousFiltrationBlocker :
      G3SelectedEquivalenceModuloPreviousFiltrationBlocker

    requestedAdditiveQuotientPrimitiveName :
      String

    requestedQuotientAPIName :
      String

    requestedPoincareGalileiIsomorphismAPIName :
      String

    requestedQuotientAPIFields :
      List String

    requestedAdditiveQuotientPrimitiveFields :
      List String

    requestedPoincareGalileiIsomorphismAPIFields :
      List String

    projectionStatus :
      G3AssociatedGradedProjectionStatus

    selectedFiltrationCarrierConstructed :
      Bool

    selectedProjectionToFiltrationConstructed :
      Bool

    selectedPreviousFiltrationInclusionConstructed :
      Bool

    acceptedQuotientCarrierConstructed :
      Bool

    acceptedProjectionConstructed :
      Bool

    exactFirstMissing :
      List G3AssociatedGradedQuotientFirstMissing

    chainResidualsStillOpen :
      List Chain.G3IWAssociatedGradedMissingPiece

    noLocalConstructionReason :
      List String

    promotionBoundary :
      List String

canonicalG3AssociatedGradedQuotientSurface :
  G3AssociatedGradedQuotientSurface
canonicalG3AssociatedGradedQuotientSurface =
  record
    { status =
        quotientSurfaceOnlyNoPromotion
    ; selectedGeneratorEvidence =
        G3.canonicalG3SelectedAssociatedGradedGalileiEvidence
    ; filteredBracketCompatibility =
        G3.canonicalG3SelectedFilteredBracketCompatibility
    ; selectedPrequotientEvidence =
        canonicalG3SelectedAssociatedGradedPrequotientEvidence
    ; selectedPreviousFiltrationInclusionEvidence =
        canonicalG3SelectedPreviousFiltrationInclusionEvidence
    ; selectedEquivalenceModuloPreviousFiltrationBlocker =
        canonicalG3SelectedEquivalenceModuloPreviousFiltrationBlocker
    ; requestedAdditiveQuotientPrimitiveName =
        "G3SelectedOperatorAdditiveQuotientPrimitive"
    ; requestedQuotientAPIName =
        "G3AssociatedGradedQuotientAPI"
    ; requestedPoincareGalileiIsomorphismAPIName =
        "G3P2IndexedPoincareGalileiIsomorphismAPI"
    ; requestedQuotientAPIFields =
        "FiltrationPiece : Nat -> Set"
        ∷ "PreviousFiltrationPiece : Nat -> Set"
        ∷ "previousIncludedInCurrent : (n : Nat) -> PreviousFiltrationPiece n -> FiltrationPiece n"
        ∷ "equivalentModuloPrevious : (n : Nat) -> WaveFunctionOperator -> WaveFunctionOperator -> Set"
        ∷ "quotientCarrier : Nat -> Set"
        ∷ "projection : (n : Nat) -> (A : WaveFunctionOperator) -> SelectedOperatorP2Degree A n -> quotientCarrier n"
        ∷ "projectionRespectsEquivalentModuloPrevious : projection descends through equivalentModuloPrevious"
        ∷ "bracketDescendsToQuotient : selected commutator descends to quotient brackets"
        ∷ []
    ; requestedAdditiveQuotientPrimitiveFields =
        "equalitySurface : G3SelectedOperatorPointwiseEqualitySurface"
        ∷ "operatorZero/operatorAddition/operatorNegation/operatorDifference tied to G3 operator definitions"
        ∷ "zeroDifferenceInPreviousFiltration : reflexivity witness for A - A in F<=n"
        ∷ "negationClosureInPreviousFiltration : symmetry witness by closure under negated differences"
        ∷ "additionClosureInPreviousFiltration : transitivity witness by closure under added differences"
        ∷ "acceptedDifferenceImageMembership : previous-filtration representative with accepted pointwise equality to the operator difference"
        ∷ []
    ; requestedPoincareGalileiIsomorphismAPIFields =
        "PoincareAtP2 : Nat -> Set"
        ∷ "poincareProjection : (n : Nat) -> PoincareAtP2 n -> quotientCarrier n"
        ∷ "galileiSection : (n : Nat) -> quotientCarrier n -> PoincareAtP2 n"
        ∷ "projectionSectionLeftInverse : poincareProjection after galileiSection is identity"
        ∷ "projectionSectionRightInverse : galileiSection after poincareProjection is identity"
        ∷ []
    ; projectionStatus =
        selectedProjectionIntoFiltrationPieceOnlyNoQuotient
    ; selectedFiltrationCarrierConstructed =
        true
    ; selectedProjectionToFiltrationConstructed =
        true
    ; selectedPreviousFiltrationInclusionConstructed =
        true
    ; acceptedQuotientCarrierConstructed =
        false
    ; acceptedProjectionConstructed =
        false
    ; exactFirstMissing =
        missingEquivalenceModuloPreviousFiltration
        ∷ missingAcceptedQuotientCarrier
        ∷ missingProjectionRespectsQuotientEquivalence
        ∷ missingP2IndexedPoincareCarrier
        ∷ missingP2IndexedPoincareGalileiIsomorphism
        ∷ []
    ; chainResidualsStillOpen =
        Chain.missingAssociatedGradedCarrier
        ∷ Chain.missingPoincareAtP2Carrier
        ∷ Chain.missingPoincareAtP2Isomorphism
        ∷ Chain.missingGalileiAssociatedGradedIdentification
        ∷ Chain.missingContractionParameterLaw
        ∷ []
    ; noLocalConstructionReason =
        "G3WaveFunctionOperatorAlgebra supplies selected generators, selected p2 degrees, and filtered bracket compatibility"
        ∷ "This module now defines the selected prequotient carrier F_n as Sigma WaveFunctionOperator (SelectedOperatorP2Degree _ n)"
        ∷ "Selected projection into F_n is concrete, and selected generators/brackets project by existing degree evidence"
        ∷ "This module now defines cumulative F<=n and a constructive previous-in-current inclusion F<=n -> F<=suc(n)"
        ∷ "It defines only a candidate relation A ~ B when waveFunctionOperatorSubtraction A B is represented by the previous cumulative filtration"
        ∷ "Pointwise operator equality/setoid laws now exist, but the candidate is not accepted as an equivalence because selected filtration subtraction/difference closure, zero difference, negation closure, addition closure, and difference image membership are absent"
        ∷ "No inspected quotient primitive constructs the quotient carrier F_n / F_{n-1} for this operator algebra"
        ∷ "Without that quotient carrier, the projection from selected operators into gr(F) cannot be accepted"
        ∷ []
    ; promotionBoundary =
        "Non-promoting surface only: this module constructs selected prequotient F_n pieces, then requests the additive quotient primitive, exact gr(F) quotient API, and p2-indexed Poincare/Galilei isomorphism API"
        ∷ "No SchrodingerPoincareToGalileiContractionCarrier is constructed here"
        ∷ "The next closure step is equivalence modulo previous filtration plus an accepted quotient carrier; after that, implement G3AssociatedGradedQuotientAPI and consume it in the contraction-parameter and SES carrier lanes"
        ∷ []
    }
