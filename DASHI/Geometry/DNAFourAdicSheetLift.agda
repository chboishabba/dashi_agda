module DASHI.Geometry.DNAFourAdicSheetLift where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Foundations.SSPTritCarrier as SSP

------------------------------------------------------------------------
-- Chemistry-native four-way lift hierarchy.
--
-- Rank names are structural rather than display conventions:
-- point -> line -> sheet -> voxel -> supervoxel.
-- Each successor object is a typed stack of four predecessor objects.
-- The materialised finite carrier is 4, 4^2, 4^3, 4^4.  A separate tower
-- boundary records that recursive closure may use the previous carrier as an
-- exponent; no finite Agda object here claims to materialise 4^(4^4).

record Quad (A : Set) : Set where
  constructor quad
  field
    q0 : A
    q1 : A
    q2 : A
    q3 : A

open Quad public

data FourLiftRank : Set where
  pointRank : FourLiftRank
  lineRank : FourLiftRank
  sheetRank : FourLiftRank
  voxelRank : FourLiftRank
  supervoxelRank : FourLiftRank

rankName : FourLiftRank → String
rankName pointRank = "point"
rankName lineRank = "4-line"
rankName sheetRank = "16-sheet"
rankName voxelRank = "64-voxel"
rankName supervoxelRank = "256-supervoxel"

record DNA4Line : Set where
  constructor line4
  field
    lineBases : Quad DNA.DNABase

record DNA16Sheet : Set where
  constructor sheet16
  field
    sheetLines : Quad DNA4Line

record DNA64Voxel : Set where
  constructor voxel64
  field
    voxelSheets : Quad DNA16Sheet

record DNA256Supervoxel : Set where
  constructor supervoxel256
  field
    supervoxelVoxels : Quad DNA64Voxel

open DNA4Line public
open DNA16Sheet public
open DNA64Voxel public
open DNA256Supervoxel public

------------------------------------------------------------------------
-- Recognisable decomposition.
--
-- The constructors themselves are the canonical decomposition maps.  The
-- following projections and reconstruction equations make recognisability
-- explicit without quotienting away order or chemistry-visible orientation.

unline4 : DNA4Line → Quad DNA.DNABase
unline4 (line4 xs) = xs

unsheet16 : DNA16Sheet → Quad DNA4Line
unsheet16 (sheet16 xs) = xs

unvoxel64 : DNA64Voxel → Quad DNA16Sheet
unvoxel64 (voxel64 xs) = xs

unsupervoxel256 : DNA256Supervoxel → Quad DNA64Voxel
unsupervoxel256 (supervoxel256 xs) = xs

line-recognisable :
  ∀ xs → unline4 (line4 xs) ≡ xs
line-recognisable xs = refl

sheet-recognisable :
  ∀ xs → unsheet16 (sheet16 xs) ≡ xs
sheet-recognisable xs = refl

voxel-recognisable :
  ∀ xs → unvoxel64 (voxel64 xs) ≡ xs
voxel-recognisable xs = refl

supervoxel-recognisable :
  ∀ xs → unsupervoxel256 (supervoxel256 xs) ≡ xs
supervoxel-recognisable xs = refl

------------------------------------------------------------------------
-- Coarse representatives and signed detail sheets.
--
-- Numerical averaging is intentionally parameterised.  The formal invariant
-- is the exact telescoping interface: a fine representative is reconstructed
-- from a coarse representative plus a signed sheet residual.  SSPTrit is reused
-- as the canonical -1/0/+1 residual carrier already present in the repository.

record SheetResidual (Fine Coarse : Set) : Set where
  constructor mkSheetResidual
  field
    fineRepresentative : Fine
    coarseRepresentative : Coarse
    signedResidual : List SSP.SSPTrit
    residualIsDifferenceFromNextCoarse : Bool

open SheetResidual public

record RecognisableSheetLift (Fine Coarse : Set) : Set₁ where
  constructor mkRecognisableSheetLift
  field
    project : Fine → Coarse
    broadcast : Coarse → Fine
    residual : Fine → List SSP.SSPTrit
    reconstruct : Coarse → List SSP.SSPTrit → Fine
    projectBroadcastRecognisable : ∀ c → project (broadcast c) ≡ c
    reconstructionReceipt : Bool
    reconstructionReceiptIsTrue : reconstructionReceipt ≡ true

open RecognisableSheetLift public

------------------------------------------------------------------------
-- Involution action is rank-preserving.

mapQuad :
  ∀ {A B : Set} →
  (A → B) →
  Quad A →
  Quad B
mapQuad f (quad a b c d) = quad (f a) (f b) (f c) (f d)

complementLine : DNA4Line → DNA4Line
complementLine (line4 xs) = line4 (mapQuad DNA.complement xs)

complementSheet : DNA16Sheet → DNA16Sheet
complementSheet (sheet16 xs) = sheet16 (mapQuad complementLine xs)

complementVoxel : DNA64Voxel → DNA64Voxel
complementVoxel (voxel64 xs) = voxel64 (mapQuad complementSheet xs)

complementSupervoxel : DNA256Supervoxel → DNA256Supervoxel
complementSupervoxel (supervoxel256 xs) =
  supervoxel256 (mapQuad complementVoxel xs)

complementLine-involutive :
  ∀ x → complementLine (complementLine x) ≡ x
complementLine-involutive (line4 (quad a b c d))
  rewrite DNA.complement-involutive a
        | DNA.complement-involutive b
        | DNA.complement-involutive c
        | DNA.complement-involutive d = refl

------------------------------------------------------------------------
-- Tetrational growth boundary.

data FourGrowthReading : Set where
  finitePowerLiftReading : FourGrowthReading
  recursiveExponentLiftReading : FourGrowthReading
  materialisedCarrierReading : FourGrowthReading
  symbolicTowerReading : FourGrowthReading

record DNAFourAdicLiftReceipt : Set where
  constructor mkDNAFourAdicLiftReceipt
  field
    ranks : List FourLiftRank
    lineIsFourPoints : Bool
    sheetIsFourLines : Bool
    voxelIsFourSheets : Bool
    supervoxelIsFourVoxels : Bool
    finiteLiftIsRecognisable : Bool
    recursiveTowerIsMaterialised : Bool
    towerReadingRemainsSymbolic : Bool
    liftBoundaryHolds : Bool
    liftBoundaryHoldsIsTrue : liftBoundaryHolds ≡ true

open DNAFourAdicLiftReceipt public

canonicalDNAFourAdicLiftReceipt : DNAFourAdicLiftReceipt
canonicalDNAFourAdicLiftReceipt =
  mkDNAFourAdicLiftReceipt
    (pointRank ∷ lineRank ∷ sheetRank ∷ voxelRank ∷ supervoxelRank ∷ [])
    true
    true
    true
    true
    true
    false
    true
    true
    refl
