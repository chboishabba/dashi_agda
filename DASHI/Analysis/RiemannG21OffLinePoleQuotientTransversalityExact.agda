module DASHI.Analysis.RiemannG21OffLinePoleQuotientTransversalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannWeilOffLineHyperbolicBlockExact as Hyperbolic

------------------------------------------------------------------------
-- Zero-side G21 gate.
--
-- #604 already owns the source-native off-line reflection-pair shape:
-- one positive and one negative hyperbolic direction.  G21 needs more:
-- those two directions must remain independent AFTER the two literal pole
-- nuisance directions are quotiented in the chosen four-sample observer.
--
-- The correct test is therefore a four-vector exterior nondegeneracy:
--
--   positive off-line response
--   negative off-line response
--   +i/2 pole profile
--   -i/2 pole profile
--
-- must span the full four-dimensional sample carrier (or the equivalent
-- quotient statement must hold).  Hyperbolic signature alone cannot prove it.
------------------------------------------------------------------------

record OffLinePoleQuotientTransversality : Set₁ where
  field
    SampleVector ExteriorValue : Set

    positiveOffLineVector negativeOffLineVector : SampleVector
    positivePoleVector negativePoleVector : SampleVector

    exterior4 :
      SampleVector → SampleVector → SampleVector → SampleVector → ExteriorValue
    ExteriorNonzero : ExteriorValue → Set

    transverseModuloPole :
      ExteriorNonzero
        (exterior4
          positiveOffLineVector
          negativeOffLineVector
          positivePoleVector
          negativePoleVector)

    transversalityReading : String

open OffLinePoleQuotientTransversality public

------------------------------------------------------------------------
-- Source signature is necessary context but not sufficient for transversality.
------------------------------------------------------------------------

canonicalSourceHyperbolicPair : Hyperbolic.HyperbolicPairBlock
canonicalSourceHyperbolicPair = Hyperbolic.hyperbolicPairBlock 0

sourceHasPositiveDirection :
  Hyperbolic.positiveIndexBeforePullback canonicalSourceHyperbolicPair ≡ 1
sourceHasPositiveDirection = refl

sourceHasNegativeDirection :
  Hyperbolic.negativeIndexBeforePullback canonicalSourceHyperbolicPair ≡ 1
sourceHasNegativeDirection = refl

------------------------------------------------------------------------
-- Tiny finite counterexample: a two-direction source can collapse to rank one
-- under an observation map.  Thus source signature (1,1) is not itself the
-- G21 quotient-rank theorem.
------------------------------------------------------------------------

data SourceDirection : Set where
  sourcePositive sourceNegative : SourceDirection

data CollapsedObservation : Set where
  sameObservedDirection : CollapsedObservation

collapsedObserver : SourceDirection → CollapsedObservation
collapsedObserver sourcePositive = sameObservedDirection
collapsedObserver sourceNegative = sameObservedDirection

sourceDirectionsDistinct : sourcePositive ≡ sourceNegative → ⊥
sourceDirectionsDistinct ()

collapsedObserverIdentifiesSourceDirections :
  collapsedObserver sourcePositive ≡ collapsedObserver sourceNegative
collapsedObserverIdentifiesSourceDirections = refl

record HyperbolicSignatureDoesNotGuaranteeObservedRank : Set where
  constructor hyperbolicSignatureDoesNotGuaranteeObservedRank
  field
    sourcePairHasTwoSignedDirections : Bool
    sourcePairHasTwoSignedDirectionsIsTrue :
      sourcePairHasTwoSignedDirections ≡ true

    observationCanCollapseThem : Bool
    observationCanCollapseThemIsTrue : observationCanCollapseThem ≡ true

canonicalHyperbolicRankBoundary : HyperbolicSignatureDoesNotGuaranteeObservedRank
canonicalHyperbolicRankBoundary =
  hyperbolicSignatureDoesNotGuaranteeObservedRank true refl true refl

------------------------------------------------------------------------
-- Positive finite witness: four independent role labels can pass the exterior
-- admission test.  This demonstrates the gate is not vacuous; it does not
-- identify these labels with literal Weil response vectors.
------------------------------------------------------------------------

data Basis4 : Set where
  eOffPlus eOffMinus ePolePlus ePoleMinus : Basis4

data ExteriorCode : Set where
  volumeZero volumeNonzero : ExteriorCode

exterior4Toy : Basis4 → Basis4 → Basis4 → Basis4 → ExteriorCode
exterior4Toy eOffPlus eOffMinus ePolePlus ePoleMinus = volumeNonzero
exterior4Toy _ _ _ _ = volumeZero

ExteriorNonzeroToy : ExteriorCode → Set
ExteriorNonzeroToy volumeZero = ⊥
ExteriorNonzeroToy volumeNonzero = ⊤

canonicalToyTransversality : OffLinePoleQuotientTransversality
canonicalToyTransversality =
  record
    { SampleVector = Basis4
    ; ExteriorValue = ExteriorCode
    ; positiveOffLineVector = eOffPlus
    ; negativeOffLineVector = eOffMinus
    ; positivePoleVector = ePolePlus
    ; negativePoleVector = ePoleMinus
    ; exterior4 = exterior4Toy
    ; ExteriorNonzero = ExteriorNonzeroToy
    ; transverseModuloPole = tt
    ; transversalityReading =
        "Finite admission witness only: two off-line directions plus two pole nuisance directions can form a nondegenerate four-vector exterior configuration. Literal Weil transversality remains to be proved."
    }

record G21ZeroSideBoundary : Set where
  constructor g21ZeroSideBoundary
  field
    sourceHyperbolicPairAlreadyOwned : Bool
    sourceHyperbolicPairAlreadyOwnedIsTrue :
      sourceHyperbolicPairAlreadyOwned ≡ true

    sourceSignatureAutomaticallyGivesPoleQuotientRankTwo : Bool
    sourceSignatureAutomaticallyGivesPoleQuotientRankTwoIsFalse :
      sourceSignatureAutomaticallyGivesPoleQuotientRankTwo ≡ false

    transversalityCriterionExecutable : Bool
    transversalityCriterionExecutableIsTrue :
      transversalityCriterionExecutable ≡ true

    literalWeilTransversalityDerived : Bool
    literalWeilTransversalityDerivedIsFalse :
      literalWeilTransversalityDerived ≡ false

canonicalG21ZeroSideBoundary : G21ZeroSideBoundary
canonicalG21ZeroSideBoundary =
  g21ZeroSideBoundary true refl false refl true refl false refl
