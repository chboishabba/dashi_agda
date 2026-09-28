module DASHI.Reasoning.Trialectic369ParticipantCenteredSSPFactorExact where

------------------------------------------------------------------------
-- PARTICIPANT-CENTERED SSP-STYLE FACTOR INSIDE THE DYADIC COMPLEMENT
--
-- DASHI CONTRIBUTION
--
-- For the AB local, the missing participant is C and the exact complement is
--
--   (AC, BC, CA, CB, CC).
--
-- Reorder this as:
--
--   incomingToC  = (AC,BC)  : T^2
--   outgoingFromC = (CA,CB) : T^2
--   selfC         = CC       : T.
--
-- Quotient only the incoming pair by simultaneous inversion.  Then:
--
--   (selfC , incomingToC / +/-) : 3 x 5 = PhaseOrbit15
--
-- while outgoingFromC remains as the exact nine-state residual.
--
-- Participant C3 relabelling cycles this construction to the BC and CA local
-- complements, so no participant is intrinsically privileged.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Reasoning.Trialectic369DyadicLocalComplementFactorizationExact as Local
import DASHI.Reasoning.Trialectic369DyadicC3LocalComplementSymmetryExact as C3
import DASHI.Reasoning.Trialectic369T5ComplementPhaseOrbitResidualExact as Quot
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction

------------------------------------------------------------------------
-- 1. C-centered interpretation of the AB complement.
------------------------------------------------------------------------

record CCenteredComplement : Set where
  constructor c-centered-complement
  field
    incomingToC : Triadic.NineSheet
    outgoingFromC : Triadic.NineSheet
    selfC : SSP.SSPTrit

open CCenteredComplement public

abComplementToCCentered :
  Local.ABComplement5 ->
  CCenteredComplement
abComplementToCCentered complement =
  c-centered-complement
    ( Reduction.sspToKernelTrit (Local.ac complement)
    , Reduction.sspToKernelTrit (Local.bc complement)
    )
    ( Reduction.sspToKernelTrit (Local.ca complement)
    , Reduction.sspToKernelTrit (Local.cb complement)
    )
    (Local.cc complement)

cCenteredToABComplement :
  CCenteredComplement ->
  Local.ABComplement5
cCenteredToABComplement
  (c-centered-complement
    (ac , bc)
    (ca , cb)
    cc) =
  Local.ab-complement5
    (Reduction.kernelToSSPTrit ac)
    (Reduction.kernelToSSPTrit bc)
    (Reduction.kernelToSSPTrit ca)
    (Reduction.kernelToSSPTrit cb)
    cc

abCCenteredRoundTrip :
  (complement : Local.ABComplement5) ->
  cCenteredToABComplement
    (abComplementToCCentered complement)
  ≡ complement
abCCenteredRoundTrip
  (Local.ab-complement5 ac bc ca cb cc)
  rewrite Reduction.sspKernelRoundTrip ac
        | Reduction.sspKernelRoundTrip bc
        | Reduction.sspKernelRoundTrip ca
        | Reduction.sspKernelRoundTrip cb = refl

cCenteredABRoundTrip :
  (state : CCenteredComplement) ->
  abComplementToCCentered
    (cCenteredToABComplement state)
  ≡ state
cCenteredABRoundTrip
  (c-centered-complement
    (ac , bc)
    (ca , cb)
    cc)
  rewrite Reduction.kernelSSPRoundTrip ac
        | Reduction.kernelSSPRoundTrip bc
        | Reduction.kernelSSPRoundTrip ca
        | Reduction.kernelSSPRoundTrip cb = refl

------------------------------------------------------------------------
-- 2. Quotient incoming observations; keep outgoing observations residual.
------------------------------------------------------------------------

participantCenteredPhaseOrbit :
  CCenteredComplement ->
  Reduction.PhaseOrbit15
participantCenteredPhaseOrbit state =
  selfC state
  , Triadic.quotientNine (incomingToC state)

participantCenteredResidual :
  CCenteredComplement ->
  Triadic.NineSheet
participantCenteredResidual =
  outgoingFromC

participantCenteredQuotient :
  CCenteredComplement ->
  Reduction.PhaseOrbit15 × Triadic.NineSheet
participantCenteredQuotient state =
  participantCenteredPhaseOrbit state
  , participantCenteredResidual state

canonicalLiftParticipantCentered :
  Reduction.PhaseOrbit15 × Triadic.NineSheet ->
  CCenteredComplement
canonicalLiftParticipantCentered
  ((phase , orbit) , outgoing) =
  c-centered-complement
    (Triadic.canonicalNineRepresentative orbit)
    outgoing
    phase

participantCenteredQuotientLiftRoundTrip :
  (state : Reduction.PhaseOrbit15 × Triadic.NineSheet) ->
  participantCenteredQuotient
    (canonicalLiftParticipantCentered state)
  ≡ state
participantCenteredQuotientLiftRoundTrip
  ((phase , orbit) , outgoing)
  rewrite Triadic.canonicalRepresentativeReturnsOrbit orbit = refl

invertIncomingToC :
  CCenteredComplement ->
  CCenteredComplement
invertIncomingToC state =
  c-centered-complement
    (Triadic.negateNine (incomingToC state))
    (outgoingFromC state)
    (selfC state)

participantCenteredQuotientInversionInvariant :
  (state : CCenteredComplement) ->
  participantCenteredQuotient
    (invertIncomingToC state)
  ≡ participantCenteredQuotient state
participantCenteredQuotientInversionInvariant
  (c-centered-complement incoming outgoing self)
  rewrite Triadic.quotientNineNegationInvariant incoming = refl

------------------------------------------------------------------------
-- 3. Agreement with the generic T5 quotient owner.
------------------------------------------------------------------------

genericQuotientAgreesWithParticipantCentered :
  (complement : Local.ABComplement5) ->
  Quot.quotientKernel5ToPhaseOrbitResidual
    (Quot.abComplementToKernel5 complement)
  ≡
  participantCenteredQuotient
    (abComplementToCCentered complement)
genericQuotientAgreesWithParticipantCentered
  (Local.ab-complement5 ac bc ca cb cc) = refl

------------------------------------------------------------------------
-- 4. C3 cycles which participant is the missing/centered one.
--
-- For AB the centered/missing participant is C.
-- After one participant relabelling the AB chart becomes old BC, so the
-- centered participant becomes old A.
-- After two relabellings it becomes old CA, centered at old B.
------------------------------------------------------------------------

data CenteredParticipant : Set where
  centeredA centeredB centeredC : CenteredParticipant

rotateCenteredParticipant :
  CenteredParticipant ->
  CenteredParticipant
rotateCenteredParticipant centeredC = centeredA
rotateCenteredParticipant centeredA = centeredB
rotateCenteredParticipant centeredB = centeredC

rotateCenteredParticipantCubed :
  (participant : CenteredParticipant) ->
  rotateCenteredParticipant
    (rotateCenteredParticipant
      (rotateCenteredParticipant participant))
  ≡ participant
rotateCenteredParticipantCubed centeredA = refl
rotateCenteredParticipantCubed centeredB = refl
rotateCenteredParticipantCubed centeredC = refl

abChartCenteredParticipant :
  CenteredParticipant
abChartCenteredParticipant =
  centeredC

abAfterOneC3CenteredParticipant :
  CenteredParticipant
abAfterOneC3CenteredParticipant =
  rotateCenteredParticipant abChartCenteredParticipant

abAfterTwoC3CenteredParticipant :
  CenteredParticipant
abAfterTwoC3CenteredParticipant =
  rotateCenteredParticipant abAfterOneC3CenteredParticipant

abAfterOneCentersA :
  abAfterOneC3CenteredParticipant ≡ centeredA
abAfterOneCentersA = refl

abAfterTwoCentersB :
  abAfterTwoC3CenteredParticipant ≡ centeredB
abAfterTwoCentersB = refl

------------------------------------------------------------------------
-- 5. Firewall.
------------------------------------------------------------------------

data ParticipantCenteredFactorIsCanonicalOggArithmeticMeaning : Set where
data OutgoingNineResidualMayBeDiscarded : Set where
data IncomingInversionIsEmpiricalObserverLaw : Set where

participantCenteredFactorNotPromotedToOggArithmeticMeaning :
  ParticipantCenteredFactorIsCanonicalOggArithmeticMeaning -> ⊥
participantCenteredFactorNotPromotedToOggArithmeticMeaning ()

outgoingResidualNotDiscarded :
  OutgoingNineResidualMayBeDiscarded -> ⊥
outgoingResidualNotDiscarded ()

incomingInversionNotPromotedToEmpiricalLaw :
  IncomingInversionIsEmpiricalObserverLaw -> ⊥
incomingInversionNotPromotedToEmpiricalLaw ()

record Trialectic369ParticipantCenteredSSPFactorBoundary : Set where
  constructor trialectic-369-participant-centered-ssp-factor-boundary
  field
    complementRechartedIncomingOutgoingSelf : Bool
    incomingPairQuotientProducesFiveOrbit : Bool
    selfCoordinateSuppliesOuterPhase : Bool
    outgoingPairRetainedAsNineResidual : Bool
    quotientCanonicalSectionPaid : Bool
    genericT5QuotientAgreementPaid : Bool
    participantC3CyclesCenteredParticipant : Bool
    canonicalOggArithmeticMeaningClaimed : Bool
    residualDiscarded : Bool

canonicalTrialectic369ParticipantCenteredSSPFactorBoundary :
  Trialectic369ParticipantCenteredSSPFactorBoundary
canonicalTrialectic369ParticipantCenteredSSPFactorBoundary =
  trialectic-369-participant-centered-ssp-factor-boundary
    true true true true true true true false false
