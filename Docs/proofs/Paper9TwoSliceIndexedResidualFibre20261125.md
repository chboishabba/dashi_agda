# Paper 9: exact two-slice fibre, signed quartic jet and indexed recovery

25 November 2026. Source-level elementary algebra and exact local SymPy. No native kernel, new physical result or novelty claim. Inspiration: user-supplied Hopf369 P0AB report and its original PR #1554, 89ebc4cf3061abba15cb297eba4f8fb3f63ab5f1, checker ca350991150f057b71abb87ad6303e74c9f5823b. The report distinguishes observation R, section I, retained complement, frame covariance and future non-descent. We transfer only that mathematical pattern, not Maxwell equations, energy, physical refinement, or numerical propagation. Original Hecke, CM, modular, polynomial symmetric-function and interpolation theory retain classical attribution.

## 1. Exact fibre, not merely a counterexample

Let F(x,y)=F(y,x) be a polynomial over Q, with centered x=X-K, y=Y-K. The existing observation is O(F)=(F(x,0),F(x,x))=(S(x),P(x)). Put u=x+y, v=xy. By elementary symmetric-polynomial theory F is a unique polynomial in u,v. The axis observation is v=0, and the diagonal is u=2x,v=x². If both vanish, F=vG; evaluating on the diagonal gives x²G(2x,x²)=0, hence G(2x,x²)=0. Divide G by the monic polynomial v-u²/4 in v: its remainder in Q[u] vanishes after u=2x, hence it is zero. Conversely the indicated product vanishes on both observations. Thus, within the symmetric ring,

    ker O = v(u²-4v) Q[u,v] = xy(x-y)² Q[x+y,xy].

This is the full fibre, with no discarded sign or zero mode. Homogeneous dimension in degree n is 0 for n<4 and floor(n/2)-1 for n>=4. The compatible n=0,1 observations satisfy P0=S0, P1=2S1. For n>=2 the explicit section is

    I_n(S_n,P_n)=S_n u^n + (P_n-2^n S_n) u^(n-2) v / 2^(n-2).

It gives O I=id and exact BIDI F=I O(F)+xy(x-y)^2 H. H has its own retained index and is unique. This is an observation-relative result, not an ambiguity in the actual full modular correspondence determined by its source. The perturbations preserve symmetry and both slices, but need not satisfy original modularity and global Hecke identities. They do prove that the two slices ALONE, even with symmetry, do not determine the general fourth/higher jet. Existing ConsumerDescentMinimalObserverExact / FactorsThrough and GovernedIndexedResidualCubeExact remain architectural owners.

## 2. Actual ramified jet consequence

In W=w^e put J-K=A W+B W²+C W³+..., A!=0. Write L=B/A², Z=C/A³, and reciprocal branches beta,beta^-1, t=beta+beta^-1. Assume beta!=0, beta!=+/-1, S2!=0 and the literal double point. The local symmetric quadratic is S2(x²-txy+y²). The cubic is S3(x³+y³)+H3(x²y+xy²), H3=P3/2-S3. Cubic relation L=(H3+(t-1)S3)/((2-t)S2) is the earlier cross. The quartic is S4(x⁴+y⁴)+U4(x³y+xy³)+V4 x²y².

The oriented branch y=beta x+delta x²+gamma x³+... has
    delta=L(beta²-beta)
    gamma=Z(beta³-beta)+2L²(beta-beta²).
No actual inverse-j analytic step is needed for the current pi consumer; these are formal series coefficient identities with A!=0, used to characterize information sufficiency. The quartic coefficient equation divided by beta² and reduced modulo beta²-t beta+1, imposing the cubic equation, is orientation-independent:

    0=(t²-4)(S2 Z+L S3)-L² S2 (t-2)(t+1)
      +(t²-2) S4+t U4+V4.

The perturbation lambda xy(x-y)² changes U4->U4+lambda, V4->V4-2lambda, preserving P4=2S4+2U4+V4. It changes the conditional normalized third jet by

    Delta Z = -lambda/[S2(t+2)].

Equivalently the original branch cubic shifts by -lambda beta(1-beta)²/[S2(beta-beta^-1)]. Do not use these divisions at t=+/-2; treat the degenerate branch separately. The kernel starts at degree 4, while the existing cross only needs the cubic local polynomial. Hence the two-slice certificate for B/A² is information-complete at its selected order; no higher-jet inference from it alone.

## 3. Minimal indexed repair, not a full dense polynomial

For homogeneous degree n, put m=floor(n/2); F_n=u^n f_n(v/u²) formally after localization, with deg f_n<=m. Along y=kx with integer k=0,1,...,m, the scalar normalized observation equals f_n(k/(1+k)²), since F_n(1,k)/(1+k)^n has that value. These nodes are distinct: for positive integers >=1 the nodes strictly decrease (and 0 gives 0). Vandermonde interpolation reconstructs f_n exactly, including all mixed coefficients. Two existing observations are k=0,1, so exactly m-1 additional independent linear scalar observations are necessary and sufficient at degree n>=2. This is a statement about information, not an algorithm to cheaply acquire each observation from the actual q-source. At quartic only k=2 is needed: kernel(1,2)=2. A single mixed coefficient U4 or V4 also suffices. Cost analysis and actual transverse coefficient producer remain open. Do not change the existing two-slice production path for pi.

## 4. Chart covariance and actual complement

Original Paper9Hecke41ChartGeometry S/T permutations act on 42 labels. The chosen pair {0,1} is sent to {41,40} by S, and {1,2} by T. A fixed label mask is not invariant. If chart action is transported, the selected mask and its 40-label complement must be transported together, using the existing corrections and inverse index maps. This is the analogue of rigid frame/refinement versus local seam, not a claim that Hecke is a cube rotation. Keep ramification e and Hecke level p separate from label and power-series order.

For the actual scalar proof, use Paper9ScalarReciprocal.diffAt / productDifference (already present). For constants c_i=K-chartValue i tau, its finite recursion T_list(Y)=prodAt(tail,Y)+head*T_tail(Y) computes (prodAt(list,Y)-prodAt(list,0))/Y without division. It includes Y=0 and repeated labels. By finite induction, T_list is continuous whenever Y and every original c_i are continuous. Bind it to restSlope via polynomial coefficient equality, or use its equality for nonzero Y plus continuity and the actual CM slice coefficient. This is the intended no-residual-derivative A5 route; original analytic germ and actual attachment not newly proved here.

## 5. Verification and correction

Executed local SymPy 1.14.0 scripts/check_paper9_two_slice_fibre.py and scripts/check_paper9_indexed_jet_recovery.py; exact committed blobs ac9fbf1e40783ee6089cf7d88508f81387dba4b3 and 986e3bc59961cfb4e451b9d0864f243ac7491af5 match local git hash-object. 19 graded kernel ranks, 81 basis divisibilities, branch perturbation, signed source orientation negative control, original selected mask S/T and 42 inverse indices; 19 canonical sections, 19 slope interpolation matrices and quartic reduction PASS. Independent local recurrence reconstruction reproduced p=5 trace -14/25, ratio 23/46656 and p=7 trace -286/343, ratio -23/55296. This is not a full p=41 GMP/analytic replay or exact prior committed script execution.

Correction to prior Lean commit ba5e748: with hp=M D-x²p, ha=N R-x²s, hT=D-R-xT, the literal goal is -N hp+M ha+NM hT, not the earlier flipped combination. Local symbolic wrong-sign negative control fails as intended. Restored correct source orientation at Lean ab9df47fff95876ec108af929bbdfe502ebf6f32. This is a source correction, not successful Lean elaboration. Lean/Lake/Agda absent. No CI. No physics, Monster, alpha, Clay, performance or novelty promotion.
