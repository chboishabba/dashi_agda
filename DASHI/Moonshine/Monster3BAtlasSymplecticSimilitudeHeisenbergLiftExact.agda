module DASHI.Moonshine.Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact where

------------------------------------------------------------------------
-- SYMPLECTIC-SIMILITUDE -> HEISENBERG LIFT WITH CENTER SCALING
--
-- The concrete ATLAS 2.Suz:2 outer generator has multiplier 2=-1 on the
-- unique inner alternating form.  Therefore the strict-Sp lift is too narrow:
-- the corresponding extraspecial-group automorphism may scale/invert the
-- center by the same multiplier.
--
-- For an additive quotient action A with
--
--     omega(Ax,Ay) = lambda * omega(x,y),
--
-- the correct central-extension lift has the form
--
--     (x,z) |-> (A x, lambda*z + q(x)).
--
-- With c the repository's asymmetric Heisenberg cocycle, q must satisfy
--
--     q(x+y) + lambda*c(x,y)
--       = q(x)+q(y)+c(Ax,Ay).
--
-- This owner exposes that exact condition generically.  For the concrete
-- primitive source word, the finite analyzer can obtain q from the symmetric
-- bilinear difference
--
--     B(x,y)=c(Ax,Ay)-lambda*c(x,y)
--
-- via q(x)=1/2 B(x,x), with 1/2=2 in F3.  Runtime instantiation is kept
-- separate from the generic kernel interface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BAtlasSymplecticBasisIntertwinerCompilerExact as Atlas

record RepositorySymplecticSimilitude : Set where
  field
    act : H.Symplectic12 → H.Symplectic12
    multiplier : Trit
    additive :
      (left right : H.Symplectic12) →
      act (Atlas.addSymplectic12 left right)
      ≡ Atlas.addSymplectic12 (act left) (act right)
    scalesPairing :
      (left right : H.Symplectic12) →
      H.symplecticPair (act left) (act right)
      ≡ H._*3_ multiplier (H.symplecticPair left right)
open RepositorySymplecticSimilitude public

record HeisenbergSimilitudeCentralCorrection
    (action : RepositorySymplecticSimilitude) : Set where
  field
    correction : H.Symplectic12 → Trit
    cocycleCoboundary :
      (left right : H.Symplectic12) →
      G._+3_
        (correction (Atlas.addSymplectic12 left right))
        (H._*3_ (multiplier action) (Atlas.heisenbergCocycle left right))
      ≡
      G._+3_
        (G._+3_ (correction left) (correction right))
        (Atlas.heisenbergCocycle (act action left) (act action right))
open HeisenbergSimilitudeCentralCorrection public

liftToHeisenbergSimilitude :
  (action : RepositorySymplecticSimilitude) →
  HeisenbergSimilitudeCentralCorrection action →
  H.Heisenberg6 → H.Heisenberg6
liftToHeisenbergSimilitude action phase element =
  H.heisenberg6
    (act action (H.quotient element))
    (G._+3_
      (H._*3_ (multiplier action) (H.centralPhase element))
      (correction phase (H.quotient element)))

record HeisenbergSimilitudeLiftRecognition
    (action : RepositorySymplecticSimilitude)
    (phase : HeisenbergSimilitudeCentralCorrection action) : Set where
  field
    preservesComposition :
      (left right : H.Heisenberg6) →
      liftToHeisenbergSimilitude action phase (H.compose left right)
      ≡ H.compose
          (liftToHeisenbergSimilitude action phase left)
          (liftToHeisenbergSimilitude action phase right)
open HeisenbergSimilitudeLiftRecognition public

record Boundary : Set where
  constructor boundary
  field
    similitudeActionInterfacePaid : Bool
    centerMultiplierLiftExposed : Bool
    similitudeCocycleCorrectionConditionExposed : Bool
    genericSimilitudeHeisenbergLiftTyped : Bool
    preferredPrimitiveConcreteCorrectionRuntimePaid : Bool
    preferredPrimitiveConcreteLiftKernelPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true true false false
