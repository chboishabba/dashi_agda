module DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import Data.Bool using (Bool; true; false)
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.OrbitProfileComputedRootSystemB4 as ORB4
open import DASHI.Physics.ShellNeighborhoodClass as SNC
open import DASHI.Physics.OrbitShellGeneratingSeriesShift as OSGS
open import DASHI.Physics.OrbitShellGeneratingSeriesRootSystemB4 as OSGB4
open import DASHI.Physics.Closure.Validation.OrbitShellSeriesComparison as OSSC
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR

data B4ShellComparisonVerdict : Set where
  exactShellMatch : B4ShellComparisonVerdict
  shellMismatch : B4ShellComparisonVerdict

data B4PromotionStatus : Set where
  standaloneOnly : B4PromotionStatus
  admissibleReady : B4PromotionStatus

record B4ShellComparisonReport : Set where
  field
    referenceLabel : String
    candidateLabel : String
    referenceShell1 : List Nat
    referenceShell2 : List Nat
    candidateShell1 : List Nat
    candidateShell2 : List Nat
    shell1Matches : Bool
    shell2Matches : Bool
    shellNeighborhood : SNC.ShellNeighborhoodClass
    seriesVerdict : OSSC.OrbitShellSeriesVerdict
    promotionStatus : B4PromotionStatus
    verdict : B4ShellComparisonVerdict

classifyShells : Bool → Bool → B4ShellComparisonVerdict
classifyShells true true = exactShellMatch
classifyShells _ _ = shellMismatch

report : B4ShellComparisonReport
report =
  let
    s1 = RPR.listNatEq OPD.shell1_p3_q1 ORB4.b4-shell1-computed
    s2 = RPR.listNatEq OPD.shell2_p3_q1 ORB4.b4-shell2-computed
  in
  record
    { referenceLabel = "signed-permutation-shift"
    ; candidateLabel = "root-system-b4-standalone"
    ; referenceShell1 = OPD.shell1_p3_q1
    ; referenceShell2 = OPD.shell2_p3_q1
    ; candidateShell1 = ORB4.b4-shell1-computed
    ; candidateShell2 = ORB4.b4-shell2-computed
    ; shell1Matches = s1
    ; shell2Matches = s2
    ; shellNeighborhood = SNC.classifyShell1Neighborhood ORB4.b4-shell1-computed
    ; seriesVerdict =
        OSSC.classifySeries
          (OSSC.compareSeries OSGS.shiftSeries OSGB4.b4Series)
    ; promotionStatus = standaloneOnly
    ; verdict = classifyShells s1 s2
    }
