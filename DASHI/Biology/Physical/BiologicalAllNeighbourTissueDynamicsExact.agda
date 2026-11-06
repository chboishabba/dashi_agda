module DASHI.Biology.Physical.BiologicalAllNeighbourTissueDynamicsExact where

------------------------------------------------------------------------
-- P2: THE ACTUAL 54-BOND OLD-FIELD COUPLED BOOLEAN TISSUE DYNAMICS
--
-- Every voxel reads ALL incident, non-periodic nearest-neighbour bonds
-- from the same previous field. This is a stronger spatial mechanism than
-- a chosen one-neighbour schedule and is not a fitted physical PNP law.
-- Local history/genome/context coordinates are preserved, and the
-- coarse future-safe projection commutes with arbitrary action traces.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid
import DASHI.Biology.Physical.BiologicalCoupledTissueCubeExact as Coupled

tritEqual : SSP.SSPTrit → SSP.SSPTrit → Bool
tritEqual SSP.sspNegOne SSP.sspNegOne = true
tritEqual SSP.sspNegOne SSP.sspZero = false
tritEqual SSP.sspNegOne SSP.sspPosOne = false
tritEqual SSP.sspZero SSP.sspNegOne = false
tritEqual SSP.sspZero SSP.sspZero = true
tritEqual SSP.sspZero SSP.sspPosOne = false
tritEqual SSP.sspPosOne SSP.sspNegOne = false
tritEqual SSP.sspPosOne SSP.sspZero = false
tritEqual SSP.sspPosOne SSP.sspPosOne = true

pointEqual : Cube.Ternary27Point → Cube.Ternary27Point → Bool
pointEqual (Cube.ternary27Point x y z) (Cube.ternary27Point a b c) =
  Bio.andB (tritEqual x a)
    (Bio.andB (tritEqual y b) (tritEqual z c))

orB : Bool → Bool → Bool
orB true b = true
orB false b = b

-- A Boolean mask keeps the two orientations of an undirected bond
-- as two reads at its respective endpoints. The physical edge itself
-- is recorded once in the canonical 54-element positive catalogue.
masked : Bool → Bool → Bool
masked = Bio.andB

junctionFine : Bio.TissueField → Cube.Ternary27Point → Bool
junctionFine fine p = Bio.junctionPresent (fine p)

junctionCoarse : Bio.CoarseTissueField → Cube.Ternary27Point → Bool
junctionCoarse coarse p = Bio.codeJunction (coarse p)

fineBondIncoming :
  Bio.TissueField → Cube.Ternary27Point → Grid.PositiveBond → Bool
fineBondIncoming fine p edge =
  orB
    (masked (pointEqual p (Grid.bondStart edge))
      (junctionFine fine (Grid.bondEnd edge)))
    (masked (pointEqual p (Grid.bondEnd edge))
      (junctionFine fine (Grid.bondStart edge)))

coarseBondIncoming :
  Bio.CoarseTissueField → Cube.Ternary27Point → Grid.PositiveBond → Bool
coarseBondIncoming coarse p edge =
  orB
    (masked (pointEqual p (Grid.bondStart edge))
      (junctionCoarse coarse (Grid.bondEnd edge)))
    (masked (pointEqual p (Grid.bondEnd edge))
      (junctionCoarse coarse (Grid.bondStart edge)))

fineListIncoming :
  Bio.TissueField → Cube.Ternary27Point → List Grid.PositiveBond → Bool
fineListIncoming fine p [] = false
fineListIncoming fine p (edge ∷ rest) =
  orB (fineBondIncoming fine p edge) (fineListIncoming fine p rest)

coarseListIncoming :
  Bio.CoarseTissueField → Cube.Ternary27Point →
  List Grid.PositiveBond → Bool
coarseListIncoming coarse p [] = false
coarseListIncoming coarse p (edge ∷ rest) =
  orB (coarseBondIncoming coarse p edge)
    (coarseListIncoming coarse p rest)

allNeighbourFine : Bio.TissueField → Cube.Ternary27Point → Bool
allNeighbourFine fine p =
  fineListIncoming fine p Grid.allPositiveBonds

allNeighbourCoarse : Bio.CoarseTissueField → Cube.Ternary27Point → Bool
allNeighbourCoarse coarse p =
  coarseListIncoming coarse p Grid.allPositiveBonds

sourceReadyFine : Bio.BiologicalState → Bool
sourceReadyFine (Bio.biologicalState g c h j e p) =
  Bio.andB g (Bio.andB h (Bio.andB j e))

sourceReadyCoarse : Bio.FutureSufficientCode → Bool
sourceReadyCoarse (Bio.futureSufficientCode g h j e p) =
  Bio.andB g (Bio.andB h (Bio.andB j e))

sourceReadCommutes :
  (state : Bio.BiologicalState) →
  sourceReadyFine state ≡ sourceReadyCoarse (Bio.project state)
sourceReadCommutes (Bio.biologicalState g c h j e p) = refl

junctionReadCommutes :
  (state : Bio.BiologicalState) →
  Bio.junctionPresent state ≡ Bio.codeJunction (Bio.project state)
junctionReadCommutes (Bio.biologicalState g c h j e p) = refl

-- No extensionality: both fields agree at EACH of the 27 voxels.
junctionAgreement :
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  Coupled.FieldsAgree fine coarse →
  (p : Cube.Ternary27Point) →
  junctionFine fine p ≡ junctionCoarse coarse p
junctionAgreement fine coarse agreement p =
  trans
    (junctionReadCommutes (fine p))
    (cong Bio.codeJunction (Coupled.atEveryVoxel agreement p))

sourceAgreement :
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  Coupled.FieldsAgree fine coarse →
  (p : Cube.Ternary27Point) →
  sourceReadyFine (fine p) ≡ sourceReadyCoarse (coarse p)
sourceAgreement fine coarse agreement p =
  trans
    (sourceReadCommutes (fine p))
    (cong sourceReadyCoarse (Coupled.atEveryVoxel agreement p))

bondIncomingAgreement :
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  (agreement : Coupled.FieldsAgree fine coarse) →
  (p : Cube.Ternary27Point)
  (edge : Grid.PositiveBond) →
  fineBondIncoming fine p edge ≡ coarseBondIncoming coarse p edge
bondIncomingAgreement fine coarse agreement p edge =
  cong₂ orB
    (cong
      (masked (pointEqual p (Grid.bondStart edge)))
      (junctionAgreement fine coarse agreement (Grid.bondEnd edge)))
    (cong
      (masked (pointEqual p (Grid.bondEnd edge)))
      (junctionAgreement fine coarse agreement (Grid.bondStart edge)))

listIncomingAgreement :
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  (agreement : Coupled.FieldsAgree fine coarse) →
  (p : Cube.Ternary27Point)
  (edges : List Grid.PositiveBond) →
  fineListIncoming fine p edges ≡ coarseListIncoming coarse p edges
listIncomingAgreement fine coarse agreement p [] = refl
listIncomingAgreement fine coarse agreement p (edge ∷ rest) =
  cong₂ orB
    (bondIncomingAgreement fine coarse agreement p edge)
    (listIncomingAgreement fine coarse agreement p rest)

allNeighbourAgreement :
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  (agreement : Coupled.FieldsAgree fine coarse) →
  (p : Cube.Ternary27Point) →
  allNeighbourFine fine p ≡ allNeighbourCoarse coarse p
allNeighbourAgreement fine coarse agreement p =
  listIncomingAgreement fine coarse agreement p Grid.allPositiveBonds

fineMorphogenicResponse :
  Bio.TissueField → Cube.Ternary27Point → Bool
fineMorphogenicResponse fine p =
  Bio.andB (sourceReadyFine (fine p)) (allNeighbourFine fine p)

coarseMorphogenicResponse :
  Bio.CoarseTissueField → Cube.Ternary27Point → Bool
coarseMorphogenicResponse coarse p =
  Bio.andB (sourceReadyCoarse (coarse p))
    (allNeighbourCoarse coarse p)

responseAgreement :
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  (agreement : Coupled.FieldsAgree fine coarse) →
  (p : Cube.Ternary27Point) →
  fineMorphogenicResponse fine p
    ≡ coarseMorphogenicResponse coarse p
responseAgreement fine coarse agreement p =
  cong₂ Bio.andB
    (sourceAgreement fine coarse agreement p)
    (allNeighbourAgreement fine coarse agreement p)

fullFineStep : Bio.Intervention → Bio.TissueField → Bio.TissueField
fullFineStep Bio.signal field p =
  Coupled.withMorphology (Bio.step Bio.signal (field p))
    (fineMorphogenicResponse field p)
fullFineStep action field p = Bio.step action (field p)

fullCoarseStep :
  Bio.Intervention → Bio.CoarseTissueField → Bio.CoarseTissueField
fullCoarseStep Bio.signal field p =
  Coupled.withCoarseMorphology (Bio.coarseStep Bio.signal (field p))
    (coarseMorphogenicResponse field p)
fullCoarseStep action field p = Bio.coarseStep action (field p)

otherActionAgreement :
  (action : Bio.Intervention)
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  (agreement : Coupled.FieldsAgree fine coarse)
  (p : Cube.Ternary27Point) →
  Bio.project (Bio.step action (fine p))
    ≡ Bio.coarseStep action (coarse p)
otherActionAgreement action fine coarse agreement p =
  trans
    (Bio.projectionCommutes action (fine p))
    (cong (Bio.coarseStep action)
      (Coupled.atEveryVoxel agreement p))

fullAgreementPreserved :
  (action : Bio.Intervention)
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  Coupled.FieldsAgree fine coarse →
  Coupled.FieldsAgree
    (fullFineStep action fine)
    (fullCoarseStep action coarse)
fullAgreementPreserved Bio.signal fine coarse agreement =
  Coupled.fieldsAgree λ p →
    trans
      (Coupled.replaceMorphologyCommutes
        (Bio.step Bio.signal (fine p))
        (fineMorphogenicResponse fine p))
      (cong₂ Coupled.withCoarseMorphology
        (otherActionAgreement Bio.signal fine coarse agreement p)
        (responseAgreement fine coarse agreement p))
fullAgreementPreserved Bio.wound fine coarse agreement =
  Coupled.fieldsAgree
    (otherActionAgreement Bio.wound fine coarse agreement)
fullAgreementPreserved Bio.connect fine coarse agreement =
  Coupled.fieldsAgree
    (otherActionAgreement Bio.connect fine coarse agreement)
fullAgreementPreserved Bio.restoreMemory fine coarse agreement =
  Coupled.fieldsAgree
    (otherActionAgreement Bio.restoreMemory fine coarse agreement)
fullAgreementPreserved Bio.provideEnvironment fine coarse agreement =
  Coupled.fieldsAgree
    (otherActionAgreement Bio.provideEnvironment fine coarse agreement)

fullFineRun :
  List Bio.Intervention → Bio.TissueField → Bio.TissueField
fullFineRun [] field = field
fullFineRun (a ∷ rest) field =
  fullFineRun rest (fullFineStep a field)

fullCoarseRun :
  List Bio.Intervention → Bio.CoarseTissueField → Bio.CoarseTissueField
fullCoarseRun [] field = field
fullCoarseRun (a ∷ rest) field =
  fullCoarseRun rest (fullCoarseStep a field)

allInterventionHistoriesPreserveFullSpatialProjection :
  (actions : List Bio.Intervention)
  (fine : Bio.TissueField)
  (coarse : Bio.CoarseTissueField) →
  Coupled.FieldsAgree fine coarse →
  Coupled.FieldsAgree
    (fullFineRun actions fine)
    (fullCoarseRun actions coarse)
allInterventionHistoriesPreserveFullSpatialProjection [] fine coarse agreement =
  agreement
allInterventionHistoriesPreserveFullSpatialProjection
  (a ∷ rest) fine coarse agreement =
  allInterventionHistoriesPreserveFullSpatialProjection rest
    (fullFineStep a fine)
    (fullCoarseStep a coarse)
    (fullAgreementPreserved a fine coarse agreement)

canonicalAllNeighboursFutureSafe :
  (actions : List Bio.Intervention)
  (fine : Bio.TissueField) →
  Coupled.FieldsAgree
    (fullFineRun actions fine)
    (fullCoarseRun actions (Bio.spatialProject fine))
canonicalAllNeighboursFutureSafe actions fine =
  allInterventionHistoriesPreserveFullSpatialProjection
    actions fine (Bio.spatialProject fine)
    (Coupled.initialFieldAgreement fine)

-- The rule is a simultaneous finite adjacency-coupled Boolean update.
-- Its proof neither establishes physical current conservation nor extends
-- the measured dmsC sequence assays to regenerative planarian dynamics.
