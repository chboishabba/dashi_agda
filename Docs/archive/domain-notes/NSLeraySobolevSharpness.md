# NS Leray/Sobolev Sharpness Receipt

Sprint 10 records the strongest current Navier-Stokes progress as a proved
negative theorem: the desired subcritical vortex-stretching absorption cannot
be obtained from Leray energy plus standard Sobolev scaling alone.

The blocked Clay lemma is:

```text
|T_stretch|
≤ epsilon * nu * ||Delta u||_2^2
  + C(E0,nu) * ||grad u||_2^2
```

The scaling counterfamily uses energy-preserving rescalings
`u_lambda(x) = lambda^(3/2) phi(lambda x)`.  It preserves `L2` energy while
the vortex-stretching term scales like `lambda^(9/2)`, beating the
subcritical right side.  This kills the Leray/Sobolev-only route.

The remaining Clay route must therefore derive additional dynamical structure
from actual Navier-Stokes evolution: vortex alignment, pressure cancellation,
or coherent cascade depletion.  None of those structures is proved here, and
`clayNavierStokesPromoted` remains false.
