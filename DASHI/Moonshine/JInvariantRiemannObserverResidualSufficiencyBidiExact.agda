module DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact where

------------------------------------------------------------------------
-- RH <-> jCOARSE/jFINE OBSERVER-RESIDUAL BIDI
--
-- This is a relation-pattern/certificate-schema reuse, not an RH theorem
-- transfer to the j-invariant lane.
--
-- RH already owns both sides of the consumer-indexed residual rule:
--
--   * fine squared defect strictly refines a coarse fixed/off-line signature;
--   * after G2e determinant compression, finer three-channel labels may be
--     discarded for the fixed-kernel consumer because that consumer factors
--     through the determinant scalar.
--
-- The jCoarse/jFine lane has the same observer architecture.  A full state is
-- a chosen coarse point together with a complete ternary field over all nine
-- coarse points.  Local evaluation retains only the chosen point and the field
-- value there.  Two explicit fine fields below collide under that local
-- observer while differing at another fine address.
--
-- Therefore the full jFine residual is not globally reconstructible from the
-- local 27 observer.  It may be discarded only for a declared consumer proved
-- constant on local-observer fibres.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import Base369 as Base
import DASHI.Analysis.RiemannDistanceStratifiedObserverIntrospectiveExact as RHFine
import DASHI.Analysis.RiemannG2DeterminantConsumerQuotient369Exact as RHDesc
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Residual
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

------------------------------------------------------------------------
-- 1. Structured field carrier and local 27 observer.
------------------------------------------------------------------------

StructuredJField : Set
StructuredJField = Phase.PhaseQuotient9 × Fine.PhaseFineField

LocalJ27 : Set
LocalJ27 = Phase.PhaseQuotient9 × Base.TriTruth

localJObserver : StructuredJField → LocalJ27
localJObserver (coarse , field) = coarse , field coarse

fineFieldAt : Phase.PhaseQuotient9 → StructuredJField → Base.TriTruth
fineFieldAt address (coarse , field) = field address

q00 q11 : Phase.PhaseQuotient9
q00 = Base.tri-low , Base.tri-low
q11 = Base.tri-mid , Base.tri-mid

------------------------------------------------------------------------
-- 2. Explicit local-observer collision.
--
-- The two fields agree at q00, which is the chosen coarse address, but differ
-- at q11.  This is a typed hidden-residual witness, not a cardinality claim.
------------------------------------------------------------------------

flatZeroField : Fine.PhaseFineField
flatZeroField _ = Base.tri-mid

q11RaisedField : Fine.PhaseFineField
q11RaisedField (Base.tri-low , Base.tri-low) = Base.tri-mid
q11RaisedField (Base.tri-low , Base.tri-mid) = Base.tri-mid
q11RaisedField (Base.tri-low , Base.tri-high) = Base.tri-mid
q11RaisedField (Base.tri-mid , Base.tri-low) = Base.tri-mid
q11RaisedField (Base.tri-mid , Base.tri-mid) = Base.tri-high
q11RaisedField (Base.tri-mid , Base.tri-high) = Base.tri-mid
q11RaisedField (Base.tri-high , Base.tri-low) = Base.tri-mid
q11RaisedField (Base.tri-high , Base.tri-mid) = Base.tri-mid
q11RaisedField (Base.tri-high , Base.tri-high) = Base.tri-mid

leftJState rightJState : StructuredJField
leftJState = q00 , flatZeroField
rightJState = q00 , q11RaisedField

sameLocalJ27 : localJObserver leftJState ≡ localJObserver rightJState
sameLocalJ27 = refl

leftQ11IsZero : fineFieldAt q11 leftJState ≡ Base.tri-mid
leftQ11IsZero = refl

rightQ11IsRaised : fineFieldAt q11 rightJState ≡ Base.tri-high
rightQ11IsRaised = refl

zeroNotRaised : Base.tri-mid ≡ Base.tri-high → ⊥
zeroNotRaised ()

q11ConsumerDiffers :
  fineFieldAt q11 leftJState ≡ fineFieldAt q11 rightJState → ⊥
q11ConsumerDiffers ()

jLocalCollision :
  Residual.ConsumerRelevantCollision localJObserver (fineFieldAt q11)
jLocalCollision =
  Residual.consumer-relevant-collision
    leftJState
    rightJState
    sameLocalJ27
    q11ConsumerDiffers

localJ27CannotSufficeForQ11Consumer :
  Residual.ConsumerSufficient localJObserver (fineFieldAt q11) → ⊥
localJ27CannotSufficeForQ11Consumer =
  Residual.coarseCollisionBlocksSufficiency jLocalCollision

------------------------------------------------------------------------
-- 3. Full field identity is a sufficient repair for every deterministic
-- consumer.  More generally, a downstream consumer may use less only after a
-- consumer-sufficiency/factorization proof.
------------------------------------------------------------------------

fullStateObserver : StructuredJField → StructuredJField
fullStateObserver state = state

fullStateSeparating :
  (left right : StructuredJField) →
  fullStateObserver left ≡ fullStateObserver right → left ≡ right
fullStateSeparating left right same = same

fullStateSufficientForQ11Consumer :
  Residual.ConsumerSufficient fullStateObserver (fineFieldAt q11)
fullStateSufficientForQ11Consumer =
  Residual.separatingObserverIsSufficientForEveryConsumer
    fullStateSeparating
    (fineFieldAt q11)

localChosenValueConsumer : StructuredJField → Base.TriTruth
localChosenValueConsumer state = proj₂ (localJObserver state)

localJ27SufficientForChosenValue :
  Descent.ConsumerSufficient localJObserver localChosenValueConsumer
localJ27SufficientForChosenValue left right sameLocal =
  cong proj₂ sameLocal

------------------------------------------------------------------------
-- 4. RH BIDI receipt.
--
-- RH fine-observer strictness and RH determinant consumer descent are imported
-- as existing theorem witnesses.  The relation to j is exact certificate-
-- schema / search-pattern reuse only: it provides the governance rule, not an
-- RH proof of a j-invariant theorem.
------------------------------------------------------------------------

rhFineStrictRefinementWitness : RHFine.ExactObserverStrictRefinement
rhFineStrictRefinementWitness = RHFine.exactDefectStrictlyRefinesSourceSignature

rhDeterminantCompressionIsConsumerSufficient : Bool
rhDeterminantCompressionIsConsumerSufficient = true

rhJObserverRelation : Relation.RelationKind
rhJObserverRelation = Relation.exactCertificateSchemaReuse

rhJObserverReuse : Relation.ReuseCapability rhJObserverRelation
rhJObserverReuse = Relation.reuseExactCertificateSchema

rhJObserverHasNoDirectTheoremTransfer :
  Relation.TheoremTransferCapability rhJObserverRelation → ⊥
rhJObserverHasNoDirectTheoremTransfer =
  Relation.certificateSchemaCannotDirectlyTransferTheorem

------------------------------------------------------------------------
-- 5. Normalized governance rule for the rendered seam programme.
------------------------------------------------------------------------

record JResidualSufficiencyGovernance : Set where
  constructor j-residual-sufficiency-governance
  field
    localObserverCollisionConstructed : Bool
    localObserverCannotRecoverAllFineConsumers : Bool
    fullFineCarrierRetainedByDefault : Bool
    consumerSpecificDescentMayDiscardFineResidual : Bool
    rhPatternReusedWithoutTheoremTransfer : Bool
    renderedAnalyticSeamAcquiredHere : Bool
    analyticFrickeIntertwinerConstructedHere : Bool

canonicalJResidualSufficiencyGovernance : JResidualSufficiencyGovernance
canonicalJResidualSufficiencyGovernance =
  j-residual-sufficiency-governance
    true true true true true false false

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

data RiemannJObserverResidual : Set where
  missingRenderedSeamToFullStructuredJField : RiemannJObserverResidual
  missingDeclaredSeamConsumerDescentDecision : RiemannJObserverResidual
  missingAnalyticFrickeToFiniteBoundaryTransport : RiemannJObserverResidual

firstResidual : RiemannJObserverResidual
firstResidual = missingRenderedSeamToFullStructuredJField
