module DASHI.Physics.YangMills.YangMillsSubmissionRound10Receipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record Round10Receipt : Set where
  field
    branchName baseCommit : String

    reciprocalFactorialDischarged : Bool
    transformedConvergenceReducedToTermParity : Bool
    alternatingOrderClosureDischarged : Bool
    ordinaryFiniteGeometricBoundDischarged : Bool
    lightweightP06LeafAdded : Bool

    concreteSineCosineInterlacingDischarged : Bool
    physicalP06InhabitantsDischarged : Bool
    polynomialWeightedShellBoundDischarged : Bool
    globalYangMillsEndpointDischarged : Bool

    verificationBoundary : String

open Round10Receipt public

round10Receipt : Round10Receipt
round10Receipt = record
  { branchName = "agent/ym-round10-concrete-bishop-stepv"
  ; baseCommit = "cbb606fdaab09557320164f1bb3b7744b7ebcd5c"
  ; reciprocalFactorialDischarged = true
  ; transformedConvergenceReducedToTermParity = true
  ; alternatingOrderClosureDischarged = true
  ; ordinaryFiniteGeometricBoundDischarged = true
  ; lightweightP06LeafAdded = true
  ; concreteSineCosineInterlacingDischarged = false
  ; physicalP06InhabitantsDischarged = false
  ; polynomialWeightedShellBoundDischarged = false
  ; globalYangMillsEndpointDischarged = false
  ; verificationBoundary =
      "The round-ten source tranche contains no explicit postulate or hole. Kernel acceptance is asserted only after the focused Agda 2.9 checker succeeds; physical and global inhabitants remain fail-closed."
  }

round10ReciprocalFactorialIsDischarged :
  reciprocalFactorialDischarged round10Receipt ≡ true
round10ReciprocalFactorialIsDischarged = refl

round10GlobalEndpointRemainsOpen :
  globalYangMillsEndpointDischarged round10Receipt ≡ false
round10GlobalEndpointRemainsOpen = refl
