module DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact where

------------------------------------------------------------------------
-- TRIALECTIC T^9 -> T^18 -> T^27 GRAPH EXTENSION
--
-- This owner closes a structural gap exposed by recent sibling work.
--
-- Existing Nongin/trialectic owners already provide:
--
--   * T^3 participant cells;
--   * T^9 = three T^3 cells in one structured dialectic;
--   * T^18 = six independent T^3 cells
--       A, B, C, S_AB, S_BC, S_CA
--     in one compatible cyclic boundary.
--
-- Recent sibling torque work reuses the same T^9/T^18 nesting, while the IIT
-- 3x3x3-cube tranche exhibits the stronger pattern that a 27-coordinate cube
-- may have only 18 free coordinates when its third T^9 face is a deterministic
-- graph over the first two faces.
--
-- The present module extracts exactly that mechanism-neutral theorem:
--
--   T^9              = one neutral three-cell coordinate chunk;
--   T^18             = two T^9 chunks, exactly rechartenable with the mature
--                       six-cell structured trialectic boundary;
--   ambient T^27     = three T^9 chunks;
--   completed T^27   = graph of an EXPLICIT completion policy T^18 -> T^9.
--
-- Thus T^18 extends to a constrained T^27 once a policy is supplied, while
-- T^18 alone does not manufacture a canonical third face.  Ambient T^27 and
-- the completed graph are not identified merely because both use 27 ternary
-- coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

------------------------------------------------------------------------
-- 1. Neutral T^9 coordinate chunk = three mature T^3 basis cells.
--
-- We deliberately do not call these left/right/synthesis here.  The same T^9
-- carrier can be consumed as a dialectic, a face, a sheet, or another typed
-- chart without smuggling one interpretation into the others.
------------------------------------------------------------------------

record T9Coordinates : Set where
  constructor t9-coordinates
  field
    coordinate0 coordinate1 coordinate2 : Cell.TrialecticBasis3Cell

open T9Coordinates public

t9CoordinateCount : Nat
t9CoordinateCount = 3 * 3

t9CoordinateCountIsNine : t9CoordinateCount ≡ 9
t9CoordinateCountIsNine = refl

cellDialecticToT9 : Cell.CellDialectic → T9Coordinates
cellDialecticToT9 dialectic =
  t9-coordinates
    (Cell.leftCell dialectic)
    (Cell.rightCell dialectic)
    (Cell.synthesisCell dialectic)

t9ToCellDialectic : T9Coordinates → Cell.CellDialectic
t9ToCellDialectic coordinates =
  Cell.cell-dialectic
    (coordinate0 coordinates)
    (coordinate1 coordinates)
    (coordinate2 coordinates)

cellDialecticT9RoundTrip :
  (dialectic : Cell.CellDialectic) →
  t9ToCellDialectic (cellDialecticToT9 dialectic) ≡ dialectic
cellDialecticT9RoundTrip (Cell.cell-dialectic a b s) = refl

t9CellDialecticRoundTrip :
  (coordinates : T9Coordinates) →
  cellDialecticToT9 (t9ToCellDialectic coordinates) ≡ coordinates
t9CellDialecticRoundTrip (t9-coordinates a b c) = refl

------------------------------------------------------------------------
-- 2. T^18 as two T^9 chunks, exactly equivalent to the mature six-cell chart.
------------------------------------------------------------------------

record T18Coordinates : Set where
  constructor t18-coordinates
  field
    firstNine secondNine : T9Coordinates

open T18Coordinates public

t18CoordinateCount : Nat
t18CoordinateCount = 2 * t9CoordinateCount

t18CoordinateCountIsEighteen : t18CoordinateCount ≡ 18
t18CoordinateCountIsEighteen = refl

structuredBoundaryCoordinatesToT18 :
  Cell.StructuredBoundaryCoordinates →
  T18Coordinates
structuredBoundaryCoordinatesToT18 coordinates =
  t18-coordinates
    (t9-coordinates
      (Cell.cellA coordinates)
      (Cell.cellB coordinates)
      (Cell.cellC coordinates))
    (t9-coordinates
      (Cell.cellSAB coordinates)
      (Cell.cellSBC coordinates)
      (Cell.cellSCA coordinates))

t18ToStructuredBoundaryCoordinates :
  T18Coordinates →
  Cell.StructuredBoundaryCoordinates
t18ToStructuredBoundaryCoordinates coordinates =
  Cell.structured-boundary-coordinates
    (coordinate0 (firstNine coordinates))
    (coordinate1 (firstNine coordinates))
    (coordinate2 (firstNine coordinates))
    (coordinate0 (secondNine coordinates))
    (coordinate1 (secondNine coordinates))
    (coordinate2 (secondNine coordinates))

structuredBoundaryT18RoundTrip :
  (coordinates : Cell.StructuredBoundaryCoordinates) →
  t18ToStructuredBoundaryCoordinates
    (structuredBoundaryCoordinatesToT18 coordinates)
  ≡ coordinates
structuredBoundaryT18RoundTrip
  (Cell.structured-boundary-coordinates a b c sab sbc sca) = refl

t18StructuredBoundaryRoundTrip :
  (coordinates : T18Coordinates) →
  structuredBoundaryCoordinatesToT18
    (t18ToStructuredBoundaryCoordinates coordinates)
  ≡ coordinates
t18StructuredBoundaryRoundTrip
  (t18-coordinates
    (t9-coordinates a b c)
    (t9-coordinates sab sbc sca)) = refl

compatibleBoundaryToT18 :
  Cell.CompatibleThreeCellTrialecticBoundary →
  T18Coordinates
compatibleBoundaryToT18 boundary =
  structuredBoundaryCoordinatesToT18
    (Cell.compatibleBoundaryToCoordinates boundary)

------------------------------------------------------------------------
-- 3. Ambient T^27 = three independent T^9 chunks.
------------------------------------------------------------------------

record T27Coordinates : Set where
  constructor t27-coordinates
  field
    face0 face1 face2 : T9Coordinates

open T27Coordinates public

t27CoordinateCount : Nat
t27CoordinateCount = 3 * t9CoordinateCount

t27CoordinateCountIsTwentySeven : t27CoordinateCount ≡ 27
t27CoordinateCountIsTwentySeven = refl

projectT18 : T27Coordinates → T18Coordinates
projectT18 cube = t18-coordinates (face0 cube) (face1 cube)

------------------------------------------------------------------------
-- 4. Graph completion: T^18 free data plus an explicit T^9 completion policy.
------------------------------------------------------------------------

T27CompletionPolicy : Set
T27CompletionPolicy = T18Coordinates → T9Coordinates

completeT27 :
  T27CompletionPolicy →
  T18Coordinates →
  T27Coordinates
completeT27 policy coordinates =
  t27-coordinates
    (firstNine coordinates)
    (secondNine coordinates)
    (policy coordinates)

projectCompleteT27 :
  (policy : T27CompletionPolicy) →
  (coordinates : T18Coordinates) →
  projectT18 (completeT27 policy coordinates) ≡ coordinates
projectCompleteT27 policy (t18-coordinates first second) = refl

GraphLaw :
  T27CompletionPolicy →
  T27Coordinates →
  Set
GraphLaw policy cube =
  face2 cube ≡ policy (projectT18 cube)

completeT27SatisfiesGraph :
  {policy : T27CompletionPolicy} →
  {coordinates : T18Coordinates} →
  GraphLaw policy (completeT27 policy coordinates)
completeT27SatisfiesGraph = refl

t27Ext :
  {left right : T27Coordinates} →
  face0 left ≡ face0 right →
  face1 left ≡ face1 right →
  face2 left ≡ face2 right →
  left ≡ right
t27Ext
  {t27-coordinates a0 a1 a2}
  {t27-coordinates b0 b1 b2}
  refl refl refl = refl

completeProjectT27UnderGraph :
  (policy : T27CompletionPolicy) →
  (cube : T27Coordinates) →
  GraphLaw policy cube →
  completeT27 policy (projectT18 cube) ≡ cube
completeProjectT27UnderGraph policy cube law =
  t27Ext refl refl (sym law)

------------------------------------------------------------------------
-- 5. Exact graph carrier.  A completed T^27 carries 27 coordinates ambiently
-- but only T^18 free data once its completion policy is fixed.
------------------------------------------------------------------------

record CompletedT27
    (policy : T27CompletionPolicy) : Set where
  constructor completed-t27
  field
    freeT18 : T18Coordinates

open CompletedT27 public

completedCube :
  {policy : T27CompletionPolicy} →
  CompletedT27 policy →
  T27Coordinates
completedCube {policy} completed =
  completeT27 policy (freeT18 completed)

completedT27FromT18 :
  (policy : T27CompletionPolicy) →
  T18Coordinates →
  CompletedT27 policy
completedT27FromT18 policy coordinates =
  completed-t27 coordinates

completedT27ProjectsExactly :
  {policy : T27CompletionPolicy} →
  (completed : CompletedT27 policy) →
  projectT18 (completedCube completed) ≡ freeT18 completed
completedT27ProjectsExactly (completed-t27 coordinates) = refl

------------------------------------------------------------------------
-- 6. No-policy firewall.
--
-- The existing T^18 boundary has six independent T^3 cells.  Nothing in that
-- carrier alone canonically chooses the additional T^9 chunk.  Recent sibling
-- work supplies concrete policies in particular domains; those remain separate
-- theorem owners until explicitly imported/welded on the same carrier.
------------------------------------------------------------------------

data T18DeterminesCanonicalT27WithoutPolicy : Set where

noCanonicalT27FromBareT18 :
  T18DeterminesCanonicalT27WithoutPolicy →
  ⊥
noCanonicalT27FromBareT18 ()

------------------------------------------------------------------------
-- 7. Promotion boundary.
------------------------------------------------------------------------

record TrialecticT9T18T27GraphExtensionBoundary : Set where
  constructor trialectic-t9-t18-t27-graph-extension-boundary
  field
    t9ChunkReusesThreeT3Cells : Bool
    t18RechartsExistingStructuredBoundary : Bool
    t27AmbientIsThreeT9Faces : Bool
    t18GraphCompletesToT27GivenPolicy : Bool
    completedT27ProjectsExactlyToT18 : Bool
    completedT27HasT18FreeData : Bool
    t18AloneDeterminesCanonicalT27 : Bool
    ambientT27IdentifiedWithCompletedGraphByCardinality : Bool
    siblingDomainCompletionAutomaticallyImported : Bool

open TrialecticT9T18T27GraphExtensionBoundary public

canonicalTrialecticT9T18T27GraphExtensionBoundary :
  TrialecticT9T18T27GraphExtensionBoundary
canonicalTrialecticT9T18T27GraphExtensionBoundary =
  trialectic-t9-t18-t27-graph-extension-boundary
    true true true true true true false false false
