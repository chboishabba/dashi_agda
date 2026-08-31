module DASHI.Analysis.RiemannG2ExistingScalarHarmonicSameObjectAttachmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Scalar

------------------------------------------------------------------------
-- SAME-OBJECT ATTACHMENT FOR EXISTING HARMONIC MACHINERY
--
-- The user-directed assumption for this BIDI tranche is that the ordinary
-- harmonic machinery already exists in the repository.  Therefore we do not
-- reconstruct Fourier/parity/moment/oscillatory-integral theory here.
--
-- What remains theorem-relevant is identity of the scalar problem itself.
-- A theorem proved for a donor problem D can be consumed by literal G2 only
-- after D is identified with the exact literal target-centred problem P.
------------------------------------------------------------------------

record ExistingScalarHarmonicDonor : Set₁ where
  field
    donorProblem : Scalar.LiteralTargetCenteredScalarProblem
    donorMachinery :
      Scalar.ExistingTargetCenteredHarmonicMachinery donorProblem
    donorReference : String

open ExistingScalarHarmonicDonor public

record SameObjectScalarHarmonicAttachment
    (D : ExistingScalarHarmonicDonor)
    (literal : Scalar.LiteralTargetCenteredScalarProblem) : Set₁ where
  field
    exactProblemIdentity : donorProblem D ≡ literal
    attachmentReference : String

open SameObjectScalarHarmonicAttachment public

attachedLiteralMachinery :
  (D : ExistingScalarHarmonicDonor) ->
  (literal : Scalar.LiteralTargetCenteredScalarProblem) ->
  SameObjectScalarHarmonicAttachment D literal ->
  Scalar.ExistingTargetCenteredHarmonicMachinery literal
attachedLiteralMachinery D literal A =
  subst
    Scalar.ExistingTargetCenteredHarmonicMachinery
    (exactProblemIdentity A)
    (donorMachinery D)

attachedLiteralCancellationReceipt :
  (D : ExistingScalarHarmonicDonor) ->
  (literal : Scalar.LiteralTargetCenteredScalarProblem) ->
  (A : SameObjectScalarHarmonicAttachment D literal) ->
  Scalar.TargetCenteredScalarCancellationReceipt literal
attachedLiteralCancellationReceipt D literal A =
  Scalar.exactConsumerReceipt (attachedLiteralMachinery D literal A)

attachedLiteralScalarConsumerClosure :
  (D : ExistingScalarHarmonicDonor) ->
  (literal : Scalar.LiteralTargetCenteredScalarProblem) ->
  (A : SameObjectScalarHarmonicAttachment D literal) ->
  Scalar.G2dScalarConsumerClosure literal
attachedLiteralScalarConsumerClosure D literal A =
  Scalar.existingMachineryClosesScalarConsumer
    literal
    (attachedLiteralMachinery D literal A)

------------------------------------------------------------------------
-- Non-descent boundary: donor theorem existence alone does not close literal G2.
------------------------------------------------------------------------

record ExistingScalarHarmonicAttachmentBoundary : Set where
  constructor existing-scalar-harmonic-attachment-boundary
  field
    ordinaryHarmonicDonorAssumedAvailable : Bool
    ordinaryHarmonicDonorAssumedAvailableIsTrue :
      ordinaryHarmonicDonorAssumedAvailable ≡ true

    donorTheoremByNameClosesLiteralG2 : Bool
    donorTheoremByNameClosesLiteralG2IsFalse :
      donorTheoremByNameClosesLiteralG2 ≡ false

    exactProblemIdentityRequired : Bool
    exactProblemIdentityRequiredIsTrue :
      exactProblemIdentityRequired ≡ true

    attachmentThenTransportsExactConsumerReceipt : Bool
    attachmentThenTransportsExactConsumerReceiptIsTrue :
      attachmentThenTransportsExactConsumerReceipt ≡ true

    scalarClosureAloneDerivesRH : Bool
    scalarClosureAloneDerivesRHIsFalse :
      scalarClosureAloneDerivesRH ≡ false

    highestAlphaReading : String

canonicalExistingScalarHarmonicAttachmentBoundary :
  ExistingScalarHarmonicAttachmentBoundary
canonicalExistingScalarHarmonicAttachmentBoundary =
  existing-scalar-harmonic-attachment-boundary
    true refl
    false refl
    true refl
    true refl
    false refl
    "Assume the repository already owns the needed parity/Fourier/moment/oscillatory theorem. The RH work is now a same-object attachment: identify that theorem's complete scalar problem record with the literal G2 target-centred determinant problem. Equality transports the exact cancellation receipt; name similarity or partial parameter agreement does not. The later balance-breaking/final contradiction consumer remains separate."
