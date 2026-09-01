module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedConcreteKernelMatchRound344Exact where

------------------------------------------------------------------------
-- ROUND344 / BIDI: THE DECLARED NESTED MAJORANT KERNEL IS THE OLD FINITE FOLD
--
-- R343 instantiates `PairIncidenceData` on the literal global nested carrier.
-- The old authority boundary `ConcreteBiotSavartKernelMatch` asks for a
-- pointwise equality between a declared concrete kernel and `pairKernelEntry`.
--
-- For the canonical nested majorant kernel there is no reason to introduce an
-- independent matrix and then prove it equal to the fold: define the concrete
-- majorant kernel to BE the old exact pair-incidence fold.  The pointwise match
-- is then definitional (`refl`).
--
-- This closes representation of the MAJORANT KERNEL only.  It intentionally
-- does not identify the signed/vector physical F_s response with that positive
-- kernel.  The remaining physical theorem is the old compact-Gamma-shaped
-- inequality:
--
--   physical F_s response <= output energy of declared majorant action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPairIncidenceRealizationRound343Exact as R343

nestedFsDeclaredMajorantKernel :
  ∀ {Row Col Scalar : Set} →
  (cutoff : Nat) →
  (S : R343.NestedFsIncidenceSemantics Row Col Scalar) →
  Row → Col → Scalar
nestedFsDeclaredMajorantKernel cutoff S =
  PairKernel.pairKernelEntry (R343.nestedFsPairIncidenceData cutoff S)

nestedFsDeclaredMajorantKernelMatch :
  ∀ {Row Col Scalar : Set}
    (cutoff : Nat)
    (S : R343.NestedFsIncidenceSemantics Row Col Scalar) →
  PairKernel.ConcreteBiotSavartKernelMatch
    (R343.nestedFsPairIncidenceData cutoff S)
    (nestedFsDeclaredMajorantKernel cutoff S)
nestedFsDeclaredMajorantKernelMatch cutoff S = record
  { pointwiseKernelMatch = λ row col → refl }

nestedFsConcreteKernelIsExactFiniteIncidenceFold :
  ∀ {Row Col Scalar : Set}
    (cutoff : Nat)
    (S : R343.NestedFsIncidenceSemantics Row Col Scalar)
    (row : Row)
    (col : Col) →
  nestedFsDeclaredMajorantKernel cutoff S row col
  ≡ PairKernel.pairKernelEntry
      (R343.nestedFsPairIncidenceData cutoff S) row col
nestedFsConcreteKernelIsExactFiniteIncidenceFold cutoff S row col = refl

round344ConcreteMajorantKernelDefinedAsOldIncidenceFold : Bool
round344ConcreteMajorantKernelDefinedAsOldIncidenceFold = true

round344PointwiseConcreteKernelMatchClosedDefinitionally : Bool
round344PointwiseConcreteKernelMatchClosedDefinitionally = true

round344NoIndependentCoarseKernelInserted : Bool
round344NoIndependentCoarseKernelInserted = true

-- The physical-response-to-majorant inequality is still a domain theorem.
round344PhysicalFsResponseBelowMajorantActionClosed : Bool
round344PhysicalFsResponseBelowMajorantActionClosed = false

round344WeightedSchurCertificateClosed : Bool
round344WeightedSchurCertificateClosed = false

round344PackageAClosed : Bool
round344PackageAClosed = false

round344ClayPromotion : Bool
round344ClayPromotion = false

round344PointwiseConcreteKernelMatchClosedDefinitionallyIsTrue :
  round344PointwiseConcreteKernelMatchClosedDefinitionally ≡ true
round344PointwiseConcreteKernelMatchClosedDefinitionallyIsTrue = refl

round344PackageAClosedIsFalse : round344PackageAClosed ≡ false
round344PackageAClosedIsFalse = refl

round344ClayPromotionIsFalse : round344ClayPromotion ≡ false
round344ClayPromotionIsFalse = refl
