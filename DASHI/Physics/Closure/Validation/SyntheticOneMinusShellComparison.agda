module DASHI.Physics.Closure.Validation.SyntheticOneMinusShellComparison where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Bool using (Bool)
open import Data.List.Base using (List)

open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.ShellNeighborhoodClass as SNC
import DASHI.Physics.SyntheticOneMinusShellRealization as SOM
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR

data SyntheticPromotionStatus : Set where
  standaloneShellOnly : SyntheticPromotionStatus
  standaloneProfileOnly : SyntheticPromotionStatus
  admissibleReady : SyntheticPromotionStatus

record SyntheticShellComparisonReport : Set where
  field
    referenceLabel : String
    candidateLabel : String
    referenceShell1 : List Nat
    candidateShell1 : List Nat
    referenceShell2 : List Nat
    candidateShell2 : List Nat
    shell1Matches : Bool
    shell2Matches : Bool
    shellNeighborhood : SNC.ShellNeighborhoodClass
    promotionStatus : SyntheticPromotionStatus

report : SyntheticShellComparisonReport
report =
  record
    { referenceLabel = "signed-permutation-shift"
    ; candidateLabel = SOM.label
    ; referenceShell1 = OPD.shell1_p3_q1
    ; candidateShell1 = SOM.shell1Profile
    ; referenceShell2 = OPD.shell2_p3_q1
    ; candidateShell2 = SOM.shell2Profile
    ; shell1Matches = RPR.listNatEq OPD.shell1_p3_q1 SOM.shell1Profile
    ; shell2Matches = RPR.listNatEq OPD.shell2_p3_q1 SOM.shell2Profile
    ; shellNeighborhood = SOM.shellNeighborhood
    ; promotionStatus = standaloneProfileOnly
    }
