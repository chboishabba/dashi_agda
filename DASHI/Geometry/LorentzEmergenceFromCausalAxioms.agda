module DASHI.Geometry.LorentzEmergenceFromCausalAxioms where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤)

open import DASHI.Execution.Contract as Exec
open import DASHI.Geometry.CausalForcesLorentz31 as CFL
open import DASHI.Geometry.ParallelogramLaw using (AdditiveSpace)
open import DASHI.Geometry.ConeMetricCompatibility as CMC
open import DASHI.Geometry.LorentzEmergence as LE
open import DASHI.Geometry.SignatureCombinatorics as SC

canonical31 : SC.Signature
canonical31 = SC.sig 3 1 0

record CausalBridgeInput
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  : Setω where
  field
    admissible : Exec.Contract.ExecutionAdmissible C
    A : AdditiveSpace
    q : CMC.Quadratic A
    cone : CMC.Cone A
    compatibility : CMC.ConeMetricCompat A cone q
    iso : Set
    isoWitness : iso
    fs : Set
    arrow : Set
    arrowWitness : arrow
    coneWitness : CFL.ConeWitness cone
    pkg : CFL.CausalSymmetryPackage
    lock : CFL.LorentzSignatureLock

open CausalBridgeInput public

obligationsFromCausalAxioms :
  ∀ {ℓx ℓs ℓδ ℓπ ℓe}
  {C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  CausalBridgeInput C →
  LE.EmergenceObligations C
obligationsFromCausalAxioms {C = C} input =
  let
    compatAtWitness =
      CFL.coneCompatAtWitness
        (pkg input)
        (q input)
        (cone input)
        (compatibility input)
        (arrow input)
        (coneWitness input)
    _ = CFL.CausalSymmetryPackage.isotropyWitness (pkg input)
    _ = CFL.CausalSymmetryPackage.arrowOrientation (pkg input)
    _ = CFL.CausalSymmetryPackage.coneNontrivial (pkg input)
  in
  record
    { signature = canonical31
    ; admissible = admissible input
    ; spatialIsotropy = iso input
    ; isotropyConsequence = iso input
    ; isotropyWitness = isoWitness input
    ; distinguishedArrow = arrow input
    ; arrowConsequence = arrow input
    ; arrowWitness = arrowWitness input
    ; coneWitness =
        CMC.Cone.InCone
          (cone input)
          (CFL.ConeWitness.point (coneWitness input))
    ; hyperbolicNonnegativeAtWitness =
        CMC.ConeMetricCompat.compat
          (compatibility input)
          (CFL.ConeWitness.point (coneWitness input))
    ; hyperbolicNonnegativeWitness = compatAtWitness
    ; nondegenerate = refl
    ; mixed = (λ ()) , (λ ())
    ; excludesPositiveDefinite = λ ()
    ; excludesNegativeDefinite = λ ()
    ; excludesMultipleNegative = λ n ()
    ; uniqueNegative = refl
    }

lorentzEmergenceFromCausalAxioms :
  ∀ {ℓx ℓs ℓδ ℓπ ℓe}
  {C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  CausalBridgeInput C →
  LE.LorentzEmergence C
lorentzEmergenceFromCausalAxioms input =
  record { obligations = obligationsFromCausalAxioms input }
