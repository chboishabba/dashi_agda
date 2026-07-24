module DASHI.Physics.YangMills.BalabanSU2TransportTelescopingExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; -R_; zeroR)
open import DASHI.Physics.YangMills.BalabanSU2AdjointRotationScalar using
  (rotationX; rotationY; rotationZ)
open import DASHI.Physics.YangMills.BalabanSU2AdjointRotationPolynomial using
  (rotationXP; rotationYP; rotationZP)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver; zeroCoefficient)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using
  (Polynomial; con; _:=_; _:+_; :-_)

------------------------------------------------------------------------
-- Exact telescoping for products of concrete SU(2) adjoint rotations.
--
-- This is the algebraic step behind
--
--   ||Pγ - I|| ≤ Σj ||Ad(qj) - I||.
--
-- No norm or order estimate is assumed here: the product displacement is
-- expanded exactly as a recursively transported sum of one-link
-- displacements.  The subsequent triangle/isometry/radius bound is therefore
-- isolated from the group algebra rather than hidden inside it.
------------------------------------------------------------------------

record Vec3R : Set where
  constructor vec3
  field
    vx vy vz : ℝ

open Vec3R public

record AdjointCoordinates : Set where
  constructor adjointCoordinates
  field
    qa qb qc qd : ℝ

open AdjointCoordinates public

zeroV : Vec3R
zeroV = vec3 zeroR zeroR zeroR

addV : Vec3R → Vec3R → Vec3R
addV (vec3 x y z) (vec3 u v w) =
  vec3 (x +R u) (y +R v) (z +R w)

negV : Vec3R → Vec3R
negV (vec3 x y z) = vec3 (-R x) (-R y) (-R z)

subV : Vec3R → Vec3R → Vec3R
subV left right = addV left (negV right)

rotate : AdjointCoordinates → Vec3R → Vec3R
rotate (adjointCoordinates a b c d) (vec3 x y z) =
  vec3
    (rotationX a b c d x y z)
    (rotationY a b c d x y z)
    (rotationZ a b c d x y z)

vecExt : ∀ {left right : Vec3R} →
  vx left ≡ vx right →
  vy left ≡ vy right →
  vz left ≡ vz right →
  left ≡ right
vecExt {vec3 x y z} {vec3 .x .y .z} refl refl refl = refl

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

rotationAddX : ∀ a b c d x y z u v w →
  rotationX a b c d (x +R u) (y +R v) (z +R w)
  ≡ rotationX a b c d x y z +R rotationX a b c d u v w
rotationAddX =
  solveComputed 10
    (λ a b c d x y z u v w →
      rotationXP a b c d (x :+ u) (y :+ v) (z :+ w)
      := rotationXP a b c d x y z :+ rotationXP a b c d u v w)
    computed

rotationAddY : ∀ a b c d x y z u v w →
  rotationY a b c d (x +R u) (y +R v) (z +R w)
  ≡ rotationY a b c d x y z +R rotationY a b c d u v w
rotationAddY =
  solveComputed 10
    (λ a b c d x y z u v w →
      rotationYP a b c d (x :+ u) (y :+ v) (z :+ w)
      := rotationYP a b c d x y z :+ rotationYP a b c d u v w)
    computed

rotationAddZ : ∀ a b c d x y z u v w →
  rotationZ a b c d (x +R u) (y +R v) (z +R w)
  ≡ rotationZ a b c d x y z +R rotationZ a b c d u v w
rotationAddZ =
  solveComputed 10
    (λ a b c d x y z u v w →
      rotationZP a b c d (x :+ u) (y :+ v) (z :+ w)
      := rotationZP a b c d x y z :+ rotationZP a b c d u v w)
    computed

rotateAdd : ∀ q left right →
  rotate q (addV left right) ≡ addV (rotate q left) (rotate q right)
rotateAdd (adjointCoordinates a b c d)
    (vec3 x y z) (vec3 u v w) =
  vecExt
    (rotationAddX a b c d x y z u v w)
    (rotationAddY a b c d x y z u v w)
    (rotationAddZ a b c d x y z u v w)

rotationNegX : ∀ a b c d x y z →
  rotationX a b c d (-R x) (-R y) (-R z)
  ≡ -R rotationX a b c d x y z
rotationNegX =
  solveComputed 7
    (λ a b c d x y z →
      rotationXP a b c d (:- x) (:- y) (:- z)
      := :- (rotationXP a b c d x y z))
    computed

rotationNegY : ∀ a b c d x y z →
  rotationY a b c d (-R x) (-R y) (-R z)
  ≡ -R rotationY a b c d x y z
rotationNegY =
  solveComputed 7
    (λ a b c d x y z →
      rotationYP a b c d (:- x) (:- y) (:- z)
      := :- (rotationYP a b c d x y z))
    computed

rotationNegZ : ∀ a b c d x y z →
  rotationZ a b c d (-R x) (-R y) (-R z)
  ≡ -R rotationZ a b c d x y z
rotationNegZ =
  solveComputed 7
    (λ a b c d x y z →
      rotationZP a b c d (:- x) (:- y) (:- z)
      := :- (rotationZP a b c d x y z))
    computed

rotateNeg : ∀ q vector →
  rotate q (negV vector) ≡ negV (rotate q vector)
rotateNeg (adjointCoordinates a b c d) (vec3 x y z) =
  vecExt
    (rotationNegX a b c d x y z)
    (rotationNegY a b c d x y z)
    (rotationNegZ a b c d x y z)

rotateSub : ∀ q left right →
  rotate q (subV left right) ≡ subV (rotate q left) (rotate q right)
rotateSub q left right =
  trans
    (rotateAdd q left (negV right))
    (cong (addV (rotate q left)) (rotateNeg q right))

subAddCancelScalar : ∀ a b c →
  (a +R (-R b)) +R (b +R (-R c)) ≡ a +R (-R c)
subAddCancelScalar =
  solveComputed 3
    (λ a b c →
      (a :+ (:- b)) :+ (b :+ (:- c)) := a :+ (:- c))
    computed

subAddCancelV : ∀ first middle last →
  addV (subV first middle) (subV middle last) ≡ subV first last
subAddCancelV (vec3 x y z) (vec3 u v w) (vec3 p q r) =
  vecExt
    (subAddCancelScalar x u p)
    (subAddCancelScalar y v q)
    (subAddCancelScalar z w r)

selfSubZeroScalar : ∀ value → value +R (-R value) ≡ zeroR
selfSubZeroScalar =
  solveComputed 1
    (λ value → value :+ (:- value) := zeroP)
    computed

selfSubZeroV : ∀ vector → subV vector vector ≡ zeroV
selfSubZeroV (vec3 x y z) =
  vecExt
    (selfSubZeroScalar x)
    (selfSubZeroScalar y)
    (selfSubZeroScalar z)

transportStepExact : ∀ q transported original →
  addV
    (rotate q (subV transported original))
    (subV (rotate q original) original)
  ≡ subV (rotate q transported) original
transportStepExact q transported original =
  trans
    (cong
      (λ first → addV first (subV (rotate q original) original))
      (rotateSub q transported original))
    (subAddCancelV
      (rotate q transported)
      (rotate q original)
      original)

transport : List AdjointCoordinates → Vec3R → Vec3R
transport [] vector = vector
transport (q ∷ path) vector = rotate q (transport path vector)

transportRemainder : List AdjointCoordinates → Vec3R → Vec3R
transportRemainder [] vector = zeroV
transportRemainder (q ∷ path) vector =
  addV
    (rotate q (transportRemainder path vector))
    (subV (rotate q vector) vector)

transportRemainderExact : ∀ path vector →
  transportRemainder path vector ≡ subV (transport path vector) vector
transportRemainderExact [] vector =
  trans
    refl
    (cong negV (selfSubZeroV vector))
transportRemainderExact (q ∷ path) vector
  rewrite transportRemainderExact path vector =
  transportStepExact q (transport path vector) vector

su2RotationLinearityLevel : ProofLevel
su2RotationLinearityLevel = computed

su2TransportTelescopingIdentityLevel : ProofLevel
su2TransportTelescopingIdentityLevel = machineChecked

su2TransportPathNormBoundLevel : ProofLevel
su2TransportPathNormBoundLevel = conditional
