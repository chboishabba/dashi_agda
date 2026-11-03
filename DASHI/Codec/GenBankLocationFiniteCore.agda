{-# OPTIONS --safe #-}
module DASHI.Codec.GenBankLocationFiniteCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

------------------------------------------------------------------------
-- Golden, generic, sequence-neutral GenBank location carrier.
-- One-based inclusive source start -> zero-based half-open internal start.
-- The width is an independent coordinate. The importer must prove/check
-- positive width and file-bound membership for every actual interval.
-- No location coordinates or DNA bases from a construct occur here.
------------------------------------------------------------------------

data Strand : Set where
  forwardStrand : Strand
  reverseStrand : Strand
  unknownStrand : Strand

reverseStrandOf : Strand → Strand
reverseStrandOf forwardStrand = reverseStrand
reverseStrandOf reverseStrand = forwardStrand
reverseStrandOf unknownStrand = unknownStrand

reverseStrandInvolutive :
  (strand : Strand) →
  reverseStrandOf (reverseStrandOf strand) ≡ strand
reverseStrandInvolutive forwardStrand = refl
reverseStrandInvolutive reverseStrand = refl
reverseStrandInvolutive unknownStrand = refl

-- First source base is one; index n is the n+1 source coordinate.
data OneBasedStart : Set where
  oneBased : Nat → OneBasedStart

sourceStart : OneBasedStart → Nat
sourceStart (oneBased n) = suc n

internalStart : OneBasedStart → Nat
internalStart (oneBased n) = n

fromInternalStart : Nat → OneBasedStart
fromInternalStart n = oneBased n

fromInternalStartRoundTrip :
  (n : Nat) →
  internalStart (fromInternalStart n) ≡ n
fromInternalStartRoundTrip n = refl

sourceInternalRoundTrip :
  (start : OneBasedStart) →
  fromInternalStart (internalStart start) ≡ start
sourceInternalRoundTrip (oneBased n) = refl

record ExactInterval : Set where
  constructor exactInterval
  field
    start : OneBasedStart
    width : Nat
    strand : Strand
open ExactInterval public

endExclusive : ExactInterval → Nat
endExclusive interval =
  internalStart (start interval) + width interval

-- For 1-based *inclusive* end and 0-based *exclusive* end, the
-- corresponding numeric value is equal; the caller must check bounds.
sourceEndInclusive : ExactInterval → Nat
sourceEndInclusive = endExclusive

endConventionMatches :
  (interval : ExactInterval) →
  sourceEndInclusive interval ≡ endExclusive interval
endConventionMatches interval = refl

data Location : Set where
  intervalLocation : ExactInterval → Location
  joinLocation : Location → Location → List Location → Location
  orderLocation : Location → Location → List Location → Location
  complementLocation : Location → Location

data FeatureRole : Set where
  sourceRole : FeatureRole
  codingRegionRole : FeatureRole
  promoterRole : FeatureRole
  replicationOriginRole : FeatureRole
  repeatRegionRole : FeatureRole
  primerBindingRole : FeatureRole
  polyASignalRole : FeatureRole
  miscellaneousRole : FeatureRole
  otherFeatureRole : FeatureRole

-- The distinction is about *evidence class*, not a claim that the
-- DNA sequence itself is a successfully engineered biological system.
data EvidenceTier : Set where
  creatorAnnotation : EvidenceTier
  sourceFileStructuralObservation : EvidenceTier
  externallyCuratedIdentityCandidate : EvidenceTier
  independentlyVerifiedSameObject : EvidenceTier

data SourceFeatureIsIndependentProteinProof : Set where
data SourceFeatureIsHumanMagnetoreception : Set where

featureLabelCannotProveProteinIdentity :
  SourceFeatureIsIndependentProteinProof → 
  SourceFeatureIsIndependentProteinProof
featureLabelCannotProveProteinIdentity impossible = impossible

-- No constructor exists for the promotion: no certificate can be made
-- solely from an annotation or a source-label string.
creatorAnnotationCannotProveHumanMagnetoreception :
  SourceFeatureIsHumanMagnetoreception →
  SourceFeatureIsHumanMagnetoreception
creatorAnnotationCannotProveHumanMagnetoreception impossible = impossible
