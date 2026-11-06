module DASHI.Moonshine.Y443JMDThreePathGraphCertificateExact where

------------------------------------------------------------------------
-- JMD y443_paths, exact source combinatorics replay in Agda.
--
-- Source: AxiomMath/CFSGCorollary/Sporadic/Monster/Y443.lean
--
-- Uses the REAL twelve Y443 node constructors, Y443.adjacent and
-- the source-exact JMD paths. Verifies every neighboring pair,
-- every separated nonneighbor pair, and distinctness of all path nodes.
-- These finite graph proofs are independent of the still-unreplayed
-- group-theoretic IsInvolutionPath/pathCoxeterElement lemmas.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMD
import DASHI.Moonshine.Y443Nonary72EquivarianceNoGoExact as Canon

andB : Bool → Bool → Bool
andB true true = true
andB _ _ = false

notB : Bool → Bool
notB true = false
notB false = true

eqNat : Nat → Nat → Bool
eqNat zero zero = true
eqNat zero (suc _) = false
eqNat (suc _) zero = false
eqNat (suc x) (suc y) = eqNat x y

eqNode : Y.Node → Y.Node → Bool
eqNode a b = eqNat (Canon.rank a) (Canon.rank b)

-- Consecutive vertices must be distinct and adjacent.
adjacentPath : List Y.Node → Bool
adjacentPath [] = true
adjacentPath (_ ∷ []) = true
adjacentPath (x ∷ y ∷ tail) =
  andB (andB (notB (eqNode x y)) (Y.adjacent x y))
       (adjacentPath (y ∷ tail))

-- Every pair separated by distance >= 2 must be distinct and nonadjacent.
farFrom : Y.Node → List Y.Node → Bool
farFrom x [] = true
farFrom x (y ∷ ys) =
  andB (andB (notB (eqNode x y)) (notB (Y.adjacent x y)))
       (farFrom x ys)

farApartPath : List Y.Node → Bool
farApartPath [] = true
farApartPath (_ ∷ []) = true
farApartPath (x ∷ y ∷ rest) =
  andB (farFrom x rest) (farApartPath (y ∷ rest))

pathGraphValid : List Y.Node → Bool
pathGraphValid path =
  andB (adjacentPath path) (farApartPath path)

jmdFirstPathGraphValid : pathGraphValid JMD.uPath ≡ true
jmdFirstPathGraphValid = refl

jmdBetaPathGraphValid : pathGraphValid JMD.betaPath ≡ true
jmdBetaPathGraphValid = refl

jmdThirdPathGraphValid : pathGraphValid JMD.thirdPath ≡ true
jmdThirdPathGraphValid = refl

x4IsNonadjacentToEntireBetaPath :
  farFrom JMD.x4 JMD.betaPath ≡ true
x4IsNonadjacentToEntireBetaPath = refl

-- This is exactly the GRAPH half of the 3 path certificates from Lean.
-- Turning adjacency into (xy)^3=1, nonadjacency into commuting
-- involutions, and path-generator recovery requires a selected
-- presented group and its genuine relation proof.
