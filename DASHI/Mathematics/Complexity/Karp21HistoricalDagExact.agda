module DASHI.Mathematics.Complexity.Karp21HistoricalDagExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE AND PROOF SCOPE
-- Richard M. Karp, "Reducibility Among Combinatorial Problems" (1972),
-- pp. 96-97, Figure 1, DOI 10.1007/978-1-4684-2001-2_9.
--
-- This is a *finite index and reachability proof* for the historical
-- 21-node, 20-edge diagram, NOT a proof that any reduction computes in
-- polynomial time, preserves yes-instances, or yields NP-completeness.
-- Source attribution for individual reductions is retained in the roadmap.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

data Problem : Set where
  sat binaryIntegerProgramming clique setPacking vertexCover
    setCover feedbackVertex feedbackArc directedHamiltonian
    undirectedHamiltonian threeSAT graphColouring cliqueCover
    exactCover hittingSet steinerTree threeDimensionalMatching
    karpKnapsack jobSequencing partition weightedMaxCut : Problem

data Edge : Set where
  e01-sat-IP e02-sat-clique e03-sat-threeSAT
    e04-clique-packing e05-clique-cover
    e06-cover-setCover e07-cover-feedbackVertex
    e08-cover-feedbackArc e09-cover-directedHamiltonian
    e10-directed-undirected e11-threeSAT-colouring
    e12-colouring-cliqueCover e13-colouring-exactCover
    e14-exactCover-hitting e15-exactCover-steiner
    e16-exactCover-threeMatching e17-exactCover-knapsack
    e18-knapsack-sequencing e19-knapsack-partition
    e20-partition-maxCut : Edge

source : Edge → Problem
source e01-sat-IP = sat
source e02-sat-clique = sat
source e03-sat-threeSAT = sat
source e04-clique-packing = clique
source e05-clique-cover = clique
source e06-cover-setCover = vertexCover
source e07-cover-feedbackVertex = vertexCover
source e08-cover-feedbackArc = vertexCover
source e09-cover-directedHamiltonian = vertexCover
source e10-directed-undirected = directedHamiltonian
source e11-threeSAT-colouring = threeSAT
source e12-colouring-cliqueCover = graphColouring
source e13-colouring-exactCover = graphColouring
source e14-exactCover-hitting = exactCover
source e15-exactCover-steiner = exactCover
source e16-exactCover-threeMatching = exactCover
source e17-exactCover-knapsack = exactCover
source e18-knapsack-sequencing = karpKnapsack
source e19-knapsack-partition = karpKnapsack
source e20-partition-maxCut = partition

target : Edge → Problem
target e01-sat-IP = binaryIntegerProgramming
target e02-sat-clique = clique
target e03-sat-threeSAT = threeSAT
target e04-clique-packing = setPacking
target e05-clique-cover = vertexCover
target e06-cover-setCover = setCover
target e07-cover-feedbackVertex = feedbackVertex
target e08-cover-feedbackArc = feedbackArc
target e09-cover-directedHamiltonian = directedHamiltonian
target e10-directed-undirected = undirectedHamiltonian
target e11-threeSAT-colouring = graphColouring
target e12-colouring-cliqueCover = cliqueCover
target e13-colouring-exactCover = exactCover
target e14-exactCover-hitting = hittingSet
target e15-exactCover-steiner = steinerTree
target e16-exactCover-threeMatching = threeDimensionalMatching
target e17-exactCover-knapsack = karpKnapsack
target e18-knapsack-sequencing = jobSequencing
target e19-knapsack-partition = partition
target e20-partition-maxCut = weightedMaxCut

allProblems : List Problem
allProblems =
  sat ∷ binaryIntegerProgramming ∷ clique ∷ setPacking ∷
  vertexCover ∷ setCover ∷ feedbackVertex ∷ feedbackArc ∷
  directedHamiltonian ∷ undirectedHamiltonian ∷ threeSAT ∷
  graphColouring ∷ cliqueCover ∷ exactCover ∷ hittingSet ∷
  steinerTree ∷ threeDimensionalMatching ∷ karpKnapsack ∷
  jobSequencing ∷ partition ∷ weightedMaxCut ∷ []

allEdges : List Edge
allEdges =
  e01-sat-IP ∷ e02-sat-clique ∷ e03-sat-threeSAT ∷
  e04-clique-packing ∷ e05-clique-cover ∷
  e06-cover-setCover ∷ e07-cover-feedbackVertex ∷
  e08-cover-feedbackArc ∷ e09-cover-directedHamiltonian ∷
  e10-directed-undirected ∷ e11-threeSAT-colouring ∷
  e12-colouring-cliqueCover ∷ e13-colouring-exactCover ∷
  e14-exactCover-hitting ∷ e15-exactCover-steiner ∷
  e16-exactCover-threeMatching ∷ e17-exactCover-knapsack ∷
  e18-knapsack-sequencing ∷ e19-knapsack-partition ∷
  e20-partition-maxCut ∷ []

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ remaining) = suc (length remaining)

twentyOneNamedNodes : length allProblems ≡ 21
twentyOneNamedNodes = refl

twentyHistoricalEdges : length allEdges ≡ 20
twentyHistoricalEdges = refl

-- The following witnesses ONLY certify graph reachability over a
-- syntactically recorded historical graph. The Edge constructors are data,
-- not polynomial reduction proof terms.
data Reachable : Problem → Set where
  satRoot : Reachable sat
  useEdge : (e : Edge) → Reachable (source e) → Reachable (target e)

allNodesHistoricallyReachable : (p : Problem) → Reachable p
allNodesHistoricallyReachable sat = satRoot
allNodesHistoricallyReachable binaryIntegerProgramming =
  useEdge e01-sat-IP satRoot
allNodesHistoricallyReachable clique =
  useEdge e02-sat-clique satRoot
allNodesHistoricallyReachable setPacking =
  useEdge e04-clique-packing (allNodesHistoricallyReachable clique)
allNodesHistoricallyReachable vertexCover =
  useEdge e05-clique-cover (allNodesHistoricallyReachable clique)
allNodesHistoricallyReachable setCover =
  useEdge e06-cover-setCover (allNodesHistoricallyReachable vertexCover)
allNodesHistoricallyReachable feedbackVertex =
  useEdge e07-cover-feedbackVertex (allNodesHistoricallyReachable vertexCover)
allNodesHistoricallyReachable feedbackArc =
  useEdge e08-cover-feedbackArc (allNodesHistoricallyReachable vertexCover)
allNodesHistoricallyReachable directedHamiltonian =
  useEdge e09-cover-directedHamiltonian (allNodesHistoricallyReachable vertexCover)
allNodesHistoricallyReachable undirectedHamiltonian =
  useEdge e10-directed-undirected (allNodesHistoricallyReachable directedHamiltonian)
allNodesHistoricallyReachable threeSAT =
  useEdge e03-sat-threeSAT satRoot
allNodesHistoricallyReachable graphColouring =
  useEdge e11-threeSAT-colouring (allNodesHistoricallyReachable threeSAT)
allNodesHistoricallyReachable cliqueCover =
  useEdge e12-colouring-cliqueCover (allNodesHistoricallyReachable graphColouring)
allNodesHistoricallyReachable exactCover =
  useEdge e13-colouring-exactCover (allNodesHistoricallyReachable graphColouring)
allNodesHistoricallyReachable hittingSet =
  useEdge e14-exactCover-hitting (allNodesHistoricallyReachable exactCover)
allNodesHistoricallyReachable steinerTree =
  useEdge e15-exactCover-steiner (allNodesHistoricallyReachable exactCover)
allNodesHistoricallyReachable threeDimensionalMatching =
  useEdge e16-exactCover-threeMatching (allNodesHistoricallyReachable exactCover)
allNodesHistoricallyReachable karpKnapsack =
  useEdge e17-exactCover-knapsack (allNodesHistoricallyReachable exactCover)
allNodesHistoricallyReachable jobSequencing =
  useEdge e18-knapsack-sequencing (allNodesHistoricallyReachable karpKnapsack)
allNodesHistoricallyReachable partition =
  useEdge e19-knapsack-partition (allNodesHistoricallyReachable karpKnapsack)
allNodesHistoricallyReachable weightedMaxCut =
  useEdge e20-partition-maxCut (allNodesHistoricallyReachable partition)
