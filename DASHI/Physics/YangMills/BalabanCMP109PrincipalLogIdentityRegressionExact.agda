module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogIdentityRegressionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The requested identity-point regression does not need a remainder estimate
-- at all.  The repository's standard compact-Lie chart already owns the local
-- inverse law
--
--       log (exp X) = X
--
-- on its explicit algebra ball.  Hence the source-convention regression
-- `log(exp xi)=xi+o(|xi|)` has ZERO remainder on that domain.  Keeping this
-- theorem separate from Federbush means any later failure of the printed
-- equation-(0.11)/(0.12) Frechet theorem cannot be blamed on the identity
-- principal-log branch.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieLinearAlgebra
open import DASHI.Physics.YangMills.CompactLieAnalyticPackage
open import DASHI.Physics.YangMills.CompactLieProofLevel

principalLogAfterExpIdentityExact :
  ∀ {g a : Level}
    {G : Set g} {𝔤 : Set a}
    {H : Group G}
    {L : LieAlgebra 𝔤}
    {R : RealLieAlgebra 𝔤 L}
    {M : QuantitativeInvariantMetric H L}
    (chart : QuantitativeLieChart H L R M)
    (xi : 𝔤) →
  InAlgebraBall chart xi →
  log chart (exp chart xi) ≡ xi
principalLogAfterExpIdentityExact chart xi inBall =
  logExp chart xi inBall

addInverseRightExact :
  ∀ {a : Level} {𝔤 : Set a}
    (L : LieAlgebra 𝔤) (xi : 𝔤) →
  add L xi (negate L xi) ≡ zero L
addInverseRightExact L xi =
  trans
    (addCommutative L xi (negate L xi))
    (additiveInverse L xi)

-- A zero remainder is stronger than little-o.  The equality below is the
-- precise regression consumed before any Federbush centre solve is involved.
principalLogIdentityRemainderIsZeroExact :
  ∀ {g a : Level}
    {G : Set g} {𝔤 : Set a}
    {H : Group G}
    {L : LieAlgebra 𝔤}
    {R : RealLieAlgebra 𝔤 L}
    {M : QuantitativeInvariantMetric H L}
    (chart : QuantitativeLieChart H L R M)
    (xi : 𝔤) →
  InAlgebraBall chart xi →
  add L (log chart (exp chart xi)) (negate L xi)
  ≡ zero L
principalLogIdentityRemainderIsZeroExact
    {L = L} chart xi inBall
  rewrite principalLogAfterExpIdentityExact chart xi inBall =
  addInverseRightExact L xi

cmp109PrincipalLogIdentityRegressionLevel : ProofLevel
cmp109PrincipalLogIdentityRegressionLevel = machineChecked

cmp109PrincipalLogIdentityZeroRemainderLevel : ProofLevel
cmp109PrincipalLogIdentityZeroRemainderLevel = machineChecked
