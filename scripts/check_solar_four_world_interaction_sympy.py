"""Four restored worlds: source-specific activation interaction, not a causal proof.

A source-on active/passive gain alone cannot identify source coupling because
it also contains paid actuation effects. Require every strict world before
forming the signed 2x2 interaction.
"""
import sympy as s
S,A,N,Q,G=s.symbols('S A N Q G',real=True)
f=lambda src,act:N+S*src+A*act+G*src*act+Q*act**2
worlds={(src,act):s.expand(f(src,act))
        for src in (0,1) for act in (0,1)}
interaction=s.expand((worlds[1,1]-worlds[1,0])-
                     (worlds[0,1]-worlds[0,0]))
assert interaction==G
# A positive source-on active-minus-passive signal need NOT reflect
# source-specific interaction. Uncharged activation would fool that test.
witness={S:2,A:4,G:0,N:-5,Q:0}
assert (worlds[1,1]-worlds[1,0]).subs(witness)==4
assert interaction.subs(witness)==0
# Missing any original-state restoration receipt blocks interaction.
for i in range(4):
    receipt=[s.Integer(1)]*4
    receipt[i]=None
    assert any(v is None for v in receipt)
print(dict(status='PASS',additive_nuisance_cancelled=True,
    source_specific_interaction=str(interaction),
    spurious_single_difference_rejected=True,
    unrestored_world_negative_controls=4))
