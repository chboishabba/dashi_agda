module DASHI.Analysis.RiemannG2ExistingScalarDonorInventoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Scalar
import DASHI.Analysis.RiemannG2ExistingScalarHarmonicSameObjectAttachmentExact as Attach
import DASHI.Analysis.DeBruijnNewmanRiemannG2RiemannSiegelBridgeExact as RS
import DASHI.Analysis.RiemannG2ExplicitFormulaBridgeAuditExact as EF
import DASHI.Analysis.RiemannAristotleG2eTargetCenteredSymmetryNoGoExact as NoGo

------------------------------------------------------------------------
-- EXISTING SCALAR DONOR INVENTORY
--
-- Search result encoded as theorem-search status, not as a claim about all
-- mathematics in the repository.  The current strongest named candidates are:
--
--   * Polymath/Riemann--Siegel finite H_t evaluation machinery;
--   * the repository explicit-formula spectral-zero architecture;
--   * exact zeta reflection/conjugation symmetry and local counting.
--
-- None of these is currently an inhabitant of
-- ExistingTargetCenteredHarmonicMachinery on the literal G2 scalar problem.
-- The first candidate has a different carrier/phase/weight language; the second
-- is a representation bridge rather than a signed cancellation receipt; the
-- third is already source-owned but fails to produce target-centred phase
-- pairing about arbitrary t.
------------------------------------------------------------------------

data DonorCandidate : Set where
  polymathRiemannSiegel
  explicitFormulaSpectralZero
  existingZetaSymmetryAndCounting
  exactLiteralTargetCenteredDonor
  : DonorCandidate

data DonorDisposition : Set where
  sharedDomainOnly
  representationBridgeOnly
  provedInsufficientForTargetPhase
  exactSameObjectCancellationDonor
  : DonorDisposition

disposition : DonorCandidate -> DonorDisposition
disposition polymathRiemannSiegel = sharedDomainOnly
disposition explicitFormulaSpectralZero = representationBridgeOnly
disposition existingZetaSymmetryAndCounting = provedInsufficientForTargetPhase
disposition exactLiteralTargetCenteredDonor = exactSameObjectCancellationDonor

rSNotDirectG2Closure :
  RS.polymath13DirectlyClosesG2 ≡ false
rSNotDirectG2Closure = RS.polymath13DirectlyClosesG2IsFalse

targetCenteredSymmetryStillOpen :
  NoGo.targetCenteredScalarCancellationClosed
    NoGo.canonicalG2eTargetCenteredSymmetryNoGo ≡ false
targetCenteredSymmetryStillOpen =
  NoGo.targetCenteredScalarCancellationClosedIsFalse
    NoGo.canonicalG2eTargetCenteredSymmetryNoGo

------------------------------------------------------------------------
-- Exact-donor admission.
--
-- Rather than inventing an ad hoc theorem name, require the repository to hand
-- us the already-existing donor as the canonical donor package.  Once supplied,
-- the previously-owned same-object attachment theorem does all transport.
------------------------------------------------------------------------

record AdmittedExistingLiteralDonor
    (literal : Scalar.LiteralTargetCenteredScalarProblem) : Set₁ where
  field
    donor : Attach.ExistingScalarHarmonicDonor
    sameObjectAttachment :
      Attach.SameObjectScalarHarmonicAttachment donor literal

open AdmittedExistingLiteralDonor public

admittedDonorClosesLiteralScalarConsumer :
  (literal : Scalar.LiteralTargetCenteredScalarProblem) ->
  AdmittedExistingLiteralDonor literal ->
  Scalar.G2dScalarConsumerClosure literal
admittedDonorClosesLiteralScalarConsumer literal admitted =
  Attach.attachedLiteralScalarConsumerClosure
    (donor admitted)
    literal
    (sameObjectAttachment admitted)

------------------------------------------------------------------------
-- Current inventory boundary.
------------------------------------------------------------------------

concreteExactLiteralDonorIdentifiedInCurrentInventory : Bool
concreteExactLiteralDonorIdentifiedInCurrentInventory = false

concreteExactLiteralDonorIdentifiedInCurrentInventoryIsFalse :
  concreteExactLiteralDonorIdentifiedInCurrentInventory ≡ false
concreteExactLiteralDonorIdentifiedInCurrentInventoryIsFalse = refl

record ExistingScalarDonorInventoryBoundary : Set where
  constructor existing-scalar-donor-inventory-boundary
  field
    rSFiniteExpressionIsExactLiteralDonor : Bool
    rSFiniteExpressionIsExactLiteralDonorIsFalse :
      rSFiniteExpressionIsExactLiteralDonor ≡ false

    explicitFormulaRepresentationAloneIsCancellationDonor : Bool
    explicitFormulaRepresentationAloneIsCancellationDonorIsFalse :
      explicitFormulaRepresentationAloneIsCancellationDonor ≡ false

    knownZetaSymmetryAndCountingCloseTargetCenteredPhase : Bool
    knownZetaSymmetryAndCountingCloseTargetCenteredPhaseIsFalse :
      knownZetaSymmetryAndCountingCloseTargetCenteredPhase ≡ false

    exactDonorPackagePlusSameObjectAttachmentWouldCloseScalarConsumer : Bool
    exactDonorPackagePlusSameObjectAttachmentWouldCloseScalarConsumerIsTrue :
      exactDonorPackagePlusSameObjectAttachmentWouldCloseScalarConsumer ≡ true

    currentInventoryHasConcreteExactDonor : Bool
    currentInventoryHasConcreteExactDonorIsFalse :
      currentInventoryHasConcreteExactDonor ≡ false

    highestAlphaReading : String

canonicalExistingScalarDonorInventoryBoundary :
  ExistingScalarDonorInventoryBoundary
canonicalExistingScalarDonorInventoryBoundary =
  existing-scalar-donor-inventory-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    "Repository search has not yet exposed a concrete theorem already packaged on the complete literal target-centred G2 scalar problem. Riemann--Siegel differs in index/phase/weights; explicit formula is representation machinery, not the signed bound; existing zeta symmetry/counting is already known insufficient about arbitrary target t. The next payment is therefore either locate a more exact existing donor or prove only the missing target-centred scalar cancellation lemma, while reusing all ordinary harmonic infrastructure."
