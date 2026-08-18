module DASHI.Moonshine.DeligneRapoportCompletedLocalNodeAuthorityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schemas de modules de courbes elliptiques",
-- Lecture Notes in Mathematics 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Robin Hartshorne,
-- "Algebraic Geometry", GTM 52, Springer, 1977.
-- DOI: 10.1007/978-1-4757-3849-0.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact LOCAL same-object theorem still required after the finite
-- Fricke branch/orbit calculation has been completed.
--
-- The source-facing theorem must provide an actual completed-local carrier at a
-- quotient singular point together with an equivalence to the two-branch
-- normalization pullback
--
--   B_0 x_k B_inf.
--
-- It must ALSO identify the two normalized branch roles with the two quotient
-- branch-orbits already derived from the Deligne--Rapoport component/Frobenius
-- action.  Therefore neither cardinality nor a generic "two branches" receipt
-- can discharge this interface.
--
-- A full formal-power-series ring is intentionally not reconstructed in this
-- branch.  This record is the proof-relevant target for an imported/proved
-- completed-local-ring theorem such as k[[x,y]]/(xy) ~= k[[x]] x_k k[[y]].
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.TwoBranchNormalizationPullbackExact as Pullback
import DASHI.Algebra.OrdinaryNodeCotangentJetExact as Jet
import DASHI.Moonshine.DeligneRapoportFrickeLocalNodeExact as Local

------------------------------------------------------------------------
-- Branch-role identification.  The finite quotient has exactly two branch
-- orbit types; the completed local normalization must name which actual branch
-- realizes each one.
------------------------------------------------------------------------

record CompletedLocalNodeAuthority : Set₁ where
  field
    ActualCompletedLocal : Set

    normalizationData : Pullback.TwoBranchNormalizationData

    toNormalizationPullback :
      ActualCompletedLocal → Pullback.NodePullback normalizationData
    fromNormalizationPullback :
      Pullback.NodePullback normalizationData → ActualCompletedLocal

    localAfterNormalization :
      (x : ActualCompletedLocal) →
      fromNormalizationPullback (toNormalizationPullback x) ≡ x

    normalizationAfterLocal :
      (x : Pullback.NodePullback normalizationData) →
      toNormalizationPullback (fromNormalizationPullback x) ≡ x

    -- Actual normalized branches corresponding to the two finite quotient
    -- branch-orbits.  Their residues must match in order to define the node.
    quotientBranch0Point : Pullback.LeftBranch normalizationData
    quotientBranch1Point : Pullback.RightBranch normalizationData

    quotientBranchesMeetAtResidue :
      Pullback.leftResidue normalizationData quotientBranch0Point
      ≡ Pullback.rightResidue normalizationData quotientBranch1Point

    -- First-order comparison: the actual completed local object admits the
    -- standard two-direction cotangent readout.  This is a deliberately weak
    -- finite shadow of the completed local ring equivalence, useful for exact
    -- regression without claiming that the jet determines the ring.
    firstJet : ActualCompletedLocal → Jet.NodeJet

open CompletedLocalNodeAuthority public

canonicalNodePoint :
  (A : CompletedLocalNodeAuthority) → ActualCompletedLocal A
canonicalNodePoint A =
  fromNormalizationPullback A
    (Pullback.reconstructCompatible
      (normalizationData A)
      (quotientBranch0Point A)
      (quotientBranch1Point A)
      (quotientBranchesMeetAtResidue A))

canonicalNodeNormalizesToDeclaredBranches :
  (A : CompletedLocalNodeAuthority) →
  toNormalizationPullback A (canonicalNodePoint A)
  ≡ Pullback.reconstructCompatible
      (normalizationData A)
      (quotientBranch0Point A)
      (quotientBranch1Point A)
      (quotientBranchesMeetAtResidue A)
canonicalNodeNormalizesToDeclaredBranches A =
  normalizationAfterLocal A
    (Pullback.reconstructCompatible
      (normalizationData A)
      (quotientBranch0Point A)
      (quotientBranch1Point A)
      (quotientBranchesMeetAtResidue A))

------------------------------------------------------------------------
-- Explicit finite branch-role adapter.
------------------------------------------------------------------------

record LocalBranchRoleCompatibility (A : CompletedLocalNodeAuthority) : Set where
  field
    branch0Role : Local.QuotientBranch2
    branch1Role : Local.QuotientBranch2
    branch0IsFiniteBranch0 : branch0Role ≡ Local.quotientBranch0
    branch1IsFiniteBranch1 : branch1Role ≡ Local.quotientBranch1
    rolesDistinct : branch0Role ≡ branch1Role → ⊥

open LocalBranchRoleCompatibility public

canonicalLocalBranchRoleCompatibility :
  (A : CompletedLocalNodeAuthority) → LocalBranchRoleCompatibility A
canonicalLocalBranchRoleCompatibility A = record
  { branch0Role = Local.quotientBranch0
  ; branch1Role = Local.quotientBranch1
  ; branch0IsFiniteBranch0 = refl
  ; branch1IsFiniteBranch1 = refl
  ; rolesDistinct = Local.quotientBranchTypesDistinct
  }

------------------------------------------------------------------------
-- Boundary: this is the target same-object authority, not an implementation of
-- Deligne--Rapoport formal geometry itself.
------------------------------------------------------------------------

record DeligneRapoportCompletedLocalNodeBoundary : Set where
  field
    actualCompletedLocalCarrierRequired : Bool
    normalizationPullbackEquivalenceRequired : Bool
    finiteBranchRolesRetained : Bool
    firstJetShadowRequired : Bool
    branchCountAloneSufficient : Bool
    completedLocalRingConstructedHere : Bool

canonicalDeligneRapoportCompletedLocalNodeBoundary :
  DeligneRapoportCompletedLocalNodeBoundary
canonicalDeligneRapoportCompletedLocalNodeBoundary = record
  { actualCompletedLocalCarrierRequired = true
  ; normalizationPullbackEquivalenceRequired = true
  ; finiteBranchRolesRetained = true
  ; firstJetShadowRequired = true
  ; branchCountAloneSufficient = false
  ; completedLocalRingConstructedHere = false
  }
