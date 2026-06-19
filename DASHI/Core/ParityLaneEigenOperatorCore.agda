module DASHI.Core.ParityLaneEigenOperatorCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ParityLaneOperatorCore as Parity

------------------------------------------------------------------------
-- Generic parity eigen/operator socket.
--
-- This module keeps the surface narrow: the lane class comes from the
-- parity bridge, the labels are plain strings, and the authority bits are
-- all closed.  Candidate-only stays true; authority, support, vector, and
-- truth stay false.

record LaneEigenSurface : Set where
  constructor mkLaneEigenSurface
  field
    laneClass :
      Parity.LaneClass

    operatorLabel :
      String

    eigenLabel :
      String

    preservationReceipt :
      String

    candidateOnly :
      Bool

    authority :
      Bool

    support :
      Bool

    vector :
      Bool

    truth :
      Bool

open LaneEigenSurface public

record HeckeLaneActionSurface : Set where
  constructor mkHeckeLaneActionSurface
  field
    heckeLaneClass :
      Parity.LaneClass

    heckeOperatorLabel :
      String

    heckeEigenLabel :
      String

    heckeLabel :
      String

    heckePreservationReceipt :
      String

    heckeCandidateOnly :
      Bool

    heckeAuthority :
      Bool

    heckeSupport :
      Bool

    heckeVector :
      Bool

    heckeTruth :
      Bool

open HeckeLaneActionSurface public

------------------------------------------------------------------------
-- Canonical eigen/operator surfaces.

canonicalOddLaneEigenSurface :
  LaneEigenSurface
canonicalOddLaneEigenSurface =
  mkLaneEigenSurface
    Parity.oddCollapsedLane
    "odd operator"
    "odd eigen"
    "odd preservation by receipt"
    true
    false
    false
    false
    false

canonicalEvenLaneEigenSurface :
  LaneEigenSurface
canonicalEvenLaneEigenSurface =
  mkLaneEigenSurface
    Parity.evenSeparatedLane
    "even operator"
    "even eigen"
    "even separation by receipt"
    true
    false
    false
    false
    false

canonicalUnresolvedLaneEigenSurface :
  LaneEigenSurface
canonicalUnresolvedLaneEigenSurface =
  mkLaneEigenSurface
    Parity.unresolvedLane
    "unresolved operator"
    "unresolved eigen"
    "candidate-only preservation"
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Canonical Hecke surfaces.

canonicalOddHeckeLaneActionSurface :
  HeckeLaneActionSurface
canonicalOddHeckeLaneActionSurface =
  mkHeckeLaneActionSurface
    Parity.oddCollapsedLane
    "odd operator"
    "odd eigen"
    "odd Hecke"
    "odd preservation by receipt"
    true
    false
    false
    false
    false

canonicalEvenHeckeLaneActionSurface :
  HeckeLaneActionSurface
canonicalEvenHeckeLaneActionSurface =
  mkHeckeLaneActionSurface
    Parity.evenSeparatedLane
    "even operator"
    "even eigen"
    "even Hecke"
    "even separation by receipt"
    true
    false
    false
    false
    false

canonicalUnresolvedHeckeLaneActionSurface :
  HeckeLaneActionSurface
canonicalUnresolvedHeckeLaneActionSurface =
  mkHeckeLaneActionSurface
    Parity.unresolvedLane
    "unresolved operator"
    "unresolved eigen"
    "unresolved Hecke"
    "candidate-only preservation"
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Socket accessors.

oddLaneClass :
  LaneEigenSurface →
  Parity.LaneClass
oddLaneClass =
  laneClass

eigenLabelOf :
  LaneEigenSurface →
  String
eigenLabelOf =
  eigenLabel

operatorLabelOf :
  LaneEigenSurface →
  String
operatorLabelOf =
  operatorLabel

heckeLabelOf :
  HeckeLaneActionSurface →
  String
heckeLabelOf =
  heckeLabel

preservationReceiptOf :
  LaneEigenSurface →
  String
preservationReceiptOf =
  preservationReceipt

------------------------------------------------------------------------
-- Projection lemmas for the canonical surfaces.

canonicalOddLaneClassIsCollapsed :
  laneClass canonicalOddLaneEigenSurface
  ≡
  Parity.oddCollapsedLane
canonicalOddLaneClassIsCollapsed =
  refl

canonicalEvenLaneClassIsSeparated :
  laneClass canonicalEvenLaneEigenSurface
  ≡
  Parity.evenSeparatedLane
canonicalEvenLaneClassIsSeparated =
  refl

canonicalUnresolvedLaneClassIsUnresolved :
  laneClass canonicalUnresolvedLaneEigenSurface
  ≡
  Parity.unresolvedLane
canonicalUnresolvedLaneClassIsUnresolved =
  refl

canonicalEigenProfileCandidateOnly :
  candidateOnly canonicalUnresolvedLaneEigenSurface
  ≡
  true
canonicalEigenProfileCandidateOnly =
  refl

vectorEigenProximityNotSupport :
  support canonicalUnresolvedLaneEigenSurface
  ≡
  false
vectorEigenProximityNotSupport =
  refl

canonicalHeckeLaneCandidateOnly :
  heckeCandidateOnly canonicalOddHeckeLaneActionSurface
  ≡
  true
canonicalHeckeLaneCandidateOnly =
  refl

oddPreservationOnlyByReceipt :
  preservationReceipt canonicalOddLaneEigenSurface
  ≡
  "odd preservation by receipt"
oddPreservationOnlyByReceipt =
  refl

evenSeparationOnlyByReceipt :
  preservationReceipt canonicalEvenLaneEigenSurface
  ≡
  "even separation by receipt"
evenSeparationOnlyByReceipt =
  refl

------------------------------------------------------------------------
-- Additional canonical accessors for the Hecke surface.

canonicalOddHeckeLaneClassIsCollapsed :
  heckeLaneClass canonicalOddHeckeLaneActionSurface
  ≡
  Parity.oddCollapsedLane
canonicalOddHeckeLaneClassIsCollapsed =
  refl

canonicalEvenHeckeLaneClassIsSeparated :
  heckeLaneClass canonicalEvenHeckeLaneActionSurface
  ≡
  Parity.evenSeparatedLane
canonicalEvenHeckeLaneClassIsSeparated =
  refl

canonicalUnresolvedHeckeLaneClassIsUnresolved :
  heckeLaneClass canonicalUnresolvedHeckeLaneActionSurface
  ≡
  Parity.unresolvedLane
canonicalUnresolvedHeckeLaneClassIsUnresolved =
  refl
