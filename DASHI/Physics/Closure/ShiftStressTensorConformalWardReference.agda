module DASHI.Physics.Closure.ShiftStressTensorConformalWardReference where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_; map)

open import DASHI.Physics.Closure.FixedPointAnalyticRGTargets as Targets
open import DASHI.Physics.Closure.ShiftFiniteScalingFusionWard as Finite
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Tangent
open import DASHI.Physics.Closure.ShiftPositionDependentOPEReference as OPE

------------------------------------------------------------------------
-- Finite stress-tensor / Ward reference.
--
-- A single discrete stress insertion is represented by the zero perturbation.
-- Correlation is a finite normalized functional and is invariant under explicit
-- translation, dilation, and special-conformal permutations of the three
-- position sites.  The resulting Ward identities are exact but finite and
-- algebraic; no continuum tensor field, derivative, or central charge exists.

data StressTensor : Set where
  stress : StressTensor

translate : OPE.Position → OPE.Position
translate OPE.left = OPE.centre
translate OPE.centre = OPE.right
translate OPE.right = OPE.left

dilate : OPE.Position → OPE.Position
dilate OPE.left = OPE.left
dilate OPE.centre = OPE.right
dilate OPE.right = OPE.centre

specialConformal : OPE.Position → OPE.Position
specialConformal OPE.left = OPE.right
specialConformal OPE.centre = OPE.centre
specialConformal OPE.right = OPE.left

stressInsertion :
  StressTensor →
  OPE.Position →
  Tangent.ShiftFinitePerturbation
stressInsertion stress x = Tangent.zeroPerturbation

wardCorrelation :
  List Tangent.ShiftFinitePerturbation →
  List OPE.Position →
  Nat
wardCorrelation operators positions = zero

DivergenceFree : Set
DivergenceFree =
  (x : OPE.Position) →
  stressInsertion stress x ≡ Tangent.zeroPerturbation

TraceCondition : Set
TraceCondition =
  (x : OPE.Position) →
  Finite.finiteScalingDimension (stressInsertion stress x) ≡ zero

TranslationWard : Set
TranslationWard =
  (operators : List Tangent.ShiftFinitePerturbation) →
  (positions : List OPE.Position) →
  wardCorrelation operators (map translate positions)
    ≡
  wardCorrelation operators positions

DilationWard : Set
DilationWard =
  (operators : List Tangent.ShiftFinitePerturbation) →
  (positions : List OPE.Position) →
  wardCorrelation operators (map dilate positions)
    ≡
  wardCorrelation operators positions

SpecialConformalWard : Set
SpecialConformalWard =
  (operators : List Tangent.ShiftFinitePerturbation) →
  (positions : List OPE.Position) →
  wardCorrelation operators (map specialConformal positions)
    ≡
  wardCorrelation operators positions

WardCompatibleWithOPE : Set
WardCompatibleWithOPE =
  (p q : Tangent.ShiftFinitePerturbation) →
  (x y : OPE.Position) →
  wardCorrelation
    (Finite._⊗p_ p q ∷ [])
    (x ∷ y ∷ [])
  ≡
  wardCorrelation
    (OPE.positionProduct p q x y ∷ [])
    (x ∷ y ∷ [])

divergenceFreeWitness : DivergenceFree
divergenceFreeWitness x = refl

traceConditionWitness : TraceCondition
traceConditionWitness x = refl

translationWardWitness : TranslationWard
translationWardWitness operators positions = refl

dilationWardWitness : DilationWard
dilationWardWitness operators positions = refl

specialConformalWardWitness : SpecialConformalWard
specialConformalWardWitness operators positions = refl

wardCompatibleWithOPEWitness : WardCompatibleWithOPE
wardCompatibleWithOPEWitness p q x y = refl

shiftStressTensorConformalWard :
  Targets.StressTensorConformalWard
    Nat OPE.Position Tangent.ShiftFinitePerturbation StressTensor
shiftStressTensorConformalWard =
  record
    { stressInsertion = stressInsertion
    ; correlation = wardCorrelation
    ; divergenceFree = DivergenceFree
    ; traceCondition = TraceCondition
    ; translationWard = TranslationWard
    ; dilationWard = DilationWard
    ; specialConformalWard = SpecialConformalWard
    ; wardCompatibleWithOPE = WardCompatibleWithOPE
    }

record ShiftStressTensorConformalWardReference : Setω where
  field
    wardTarget :
      Targets.StressTensorConformalWard
        Nat OPE.Position Tangent.ShiftFinitePerturbation StressTensor
    divergenceFreeLaw : DivergenceFree
    traceLaw : TraceCondition
    translationLaw : TranslationWard
    dilationLaw : DilationWard
    specialConformalLaw : SpecialConformalWard
    opeCompatibility : WardCompatibleWithOPE
    nonClaimBoundary : List String

open ShiftStressTensorConformalWardReference public

canonicalShiftStressTensorConformalWardReference :
  ShiftStressTensorConformalWardReference
canonicalShiftStressTensorConformalWardReference =
  record
    { wardTarget = shiftStressTensorConformalWard
    ; divergenceFreeLaw = divergenceFreeWitness
    ; traceLaw = traceConditionWitness
    ; translationLaw = translationWardWitness
    ; dilationLaw = dilationWardWitness
    ; specialConformalLaw = specialConformalWardWitness
    ; opeCompatibility = wardCompatibleWithOPEWitness
    ; nonClaimBoundary =
        "ShiftStressTensorConformalWardReference supplies exact finite Ward identities under three explicit site transformations"
        ∷ "the stress insertion is the zero perturbation and is exactly divergence-free and trace-zero on the finite carrier"
        ∷ "Ward compatibility is proved against the finite position-dependent OPE product"
        ∷ "the normalized correlation functional is finite and identically zero"
        ∷ "No continuum stress tensor, distributional conservation law, central charge, anomaly, or physical conformal Ward theorem is claimed"
        ∷ []
    }
