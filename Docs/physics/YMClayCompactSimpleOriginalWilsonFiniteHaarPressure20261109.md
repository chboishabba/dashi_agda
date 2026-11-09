# General compact-simple-G original Wilson finite-volume Haar pressure bound

Date: 9 November 2026. **Mathematical analytic result for the original finite Wilson measures**. No claim of continuum Yang–Mills, physically uniform connecting-polymer decay, spectral gap, or G1.03 Clay completion.

## Source and group hypotheses

Fix any compact connected Lie group `G` of dimension `d_G` (in particular any compact simple Lie group, including allowed global forms) and a selected **faithful finite-dimensional unitary Wilson representation** `rho:G->U(k)`. Fix any bi-invariant Riemannian metric on `G`, with geodesic distance `dist_G`, and normalized Haar `H_G`.

Standard compact Lie group/representation geometry supplies the following *genuine group-dependent but volume-independent constants*:

1. `L_G<infinity` with `||rho(g)-I||_HS/sqrt(k) <= L_G dist_G(e,g)` for all `g∈G`. This follows by bounding the derivative `d rho` on the compact unit tangent sphere and integrating along a minimizing geodesic. For disconnected groups (not needed here) use their connected component separately.
2. `delta_G>0` and `c_G∈(0,1]` with `H_G(B_delta(e)) >= c_G delta^(d_G)` for `0<delta<=delta_G`. In a normal coordinate chart, smooth positive Haar density is bounded below on a sufficiently small closed ball. Shrink `delta_G` to `<=1` if necessary.

These constants depend on the *actual chosen group and representation*, not on bare coupling `beta`, volume or lattice spacing.

## Original Wilson finite-volume theorem

On the periodic four-dimensional hypercubic lattice with `V` sites, `L=4V` positive links and `P=6V` unoriented plaquettes, put

```
t_rho(U_p) = Re Tr rho(U_p)/k,
Z_{G,V}(beta) = int exp(beta sum_p t_rho(U_p)) prod_l dH_G(U_l),
p_{G,V}(beta) = (1/P) log Z_{G,V}(beta).
```

For any `beta >= beta_G := max(1,delta_G^(-2))`, put `delta=beta^(-1/2)`. Restrict the SAME original normalized product-Haar integral to configurations with every one of the `L` link variables in `B_delta(e)`. By the bi-invariant metric triangle inequality, every four-factor oriented plaquette holonomy lies within distance `4delta` of identity. The exact normalized unitary trace identity gives

```
1-t_rho(g) = ||rho(g)-I||_HS^2/(2k)
            <= (L_G^2/2) dist_G(e,g)^2.
```

Therefore on that event `t_rho(U_p)>=1-8 L_G^2 delta^2`. Independence of the **reference Haar product only** (not of the Wilson Gibbs plaquettes) gives its actual mass at least `(c_G delta^(d_G))^L`. Hence

```
Z_{G,V}(beta) >=
  exp(beta P - 8 L_G^2 P) * (c_G beta^(-d_G/2))^L,

p_{G,V}(beta) >=
  beta - 8 L_G^2 - (2/3) log(1/c_G) - (d_G/3) log beta.
```

The finite compact-group partition pressure `p_{G,V}` is smooth and convex since `p''_{G,V}(beta)=Var_beta(sum_p t_rho(U_p))/P>=0` and `p_{G,V}(0)=0`. Thus `p'_{G,V}(beta)>=p_{G,V}(beta)/beta`. Periodic translation and orientation symmetry imply each original plaquette has the same expectation, yielding

```
0 <= E_{G,beta,V}[1-t_rho(U_p)]
   <= [8 L_G^2 + (2/3)log(1/c_G)
                 + (d_G/3) log beta] / beta,
                    beta>=beta_G.
```

**This theorem is uniform in the original finite volume for each chosen G**. It applies to any compact simple group with group-dependent constants, provided the original faithful Wilson representation and Haar geometry are selected. It does not assert the same constants uniformly over the class of all groups.

## Stronger large-deviation corollary on the SAME original Wilson law

Define `B_epsilon=(# {p:1-t_rho(U_p)>=epsilon})/P`. Since `D(U)=sum_p(1-t_rho(U_p))>=epsilon eta P` on `{B_epsilon>=eta}`, bound the original restricted numerator by `exp(beta P-beta epsilon eta P)`. Using the above original partition lower bound gives

```
Pr_{G,beta,V}(B_epsilon>=eta)
 <= min(1, exp[-P (beta epsilon eta-C_G(beta))]),

C_G(beta) =
 8 L_G^2 + (2/3)log(1/c_G) + (d_G/3)log beta,
beta>=beta_G, epsilon>0, 0<eta<=1.
```

The proof is *exactly on the true source Wilson measure*: the reference product Haar law normalizes to one; no independent plaquette measure, fake i.i.d. assumption, Markov-chain mixing or selected T5 rational carrier has been inserted.

## What has actually advanced

**Finite G1.02 original-source mathematical scope:** an elementary group-uniform-in-volume Wilson plaquette-deficit and extensive-bad-density theorem for each compact simple G (indeed compact connected G), assuming only genuine smooth compact Lie/Haar and selected unitary Wilson representation facts. This replaces SU(2)-only quaternion geometry with exact general compact-group differential geometry.

**Still OPEN:** actual N-index/representation normalization if the Clay group choice fixes a different Wilson action; physically renormalized beta(a) trajectory; fixed-physical-size gauge-invariant noncollapse; actual E1.03 interacting four-dimensional limit; D1.03 **spatially connecting bad-polymer** activity versus entropy; D2 common-exponent dense original OS tests; N1.02 nontriviality; G1.03 full E1/D2/N1 construction for arbitrary compact simple G. A rare extensive bad density does not prevent arbitrarily long sparse bad paths. Native Agda 2.9 acceptance is unavailable; this is a complete mathematical finite-source derivation, not an Agda theorem in the selected G carrier.

Attribution: Wilson finite lattice gauge theory; compact Lie bi-invariant Riemannian metrics and Haar measure; elementary unitary representation norm and Gibbs pressure convexity. The construction is integrated with DASHI G1.02, not observer/TSVF/KK.
