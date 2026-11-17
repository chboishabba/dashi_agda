#!/usr/bin/env python3
"""Actual Monster 3B central-phase probe from a published mmgroup word.

Primary computational source: Martin Seysen, mmgroup
applications/Hurwitz/find_generators.py (find_type_3B, tests chi=53),
applications/Hurwitz/hurwitz_monster_samples.py (first literal g3 word),
source blob f618df5f903b08d212e4d03b95617159f7fd5842.
This is a genuine Monster 3B element, NOT a source-aligned
E=3^(1+12) generating set.

Dependency: mmgroup (not installed in the local evaluation environment).
No successful run, rank receipt, or Monster intertwiner is asserted.
"""
import hashlib
import json

# Literal g3 from first published Hurwitz sample, in the distinguished
# 2B-centralizer and of Monster class 3B (verified by the producer).
SOURCE_URL = ("https://github.com/Martin-Seysen/mmgroup/blob/master/"
              "applications/Hurwitz/hurwitz_monster_samples.py")
G3_WORD = "M0<y_0dah*x_0c8bh*d_468h*p_45301176*l_2*p_79432320>"

def select_zeta(v, z):
    """Eigenspace projector (1+zeta^-1 Z+zeta^-2 Z²)/3 over GF(7).

    mmgroup vectors have a right action by Monster elements.
    2 is a primitive third root in GF(7), so 1/3=5 mod 7.
    """
    return 5 * (v + 4 * (v * z) + 2 * (v * (z**2)))

def run():
    try:
        from mmgroup import MM, MMV
        from importlib.metadata import version
    except ImportError as exc:
        raise SystemExit(
            "UNAVAILABLE: requires installed mmgroup package and its "
            "196884-dimensional Monster representation; no synthetic replacement"
        ) from exc
    z = MM(G3_WORD)
    if z.order() != 3 or not z.in_G_x0():
        raise RuntimeError("source g3 word did not realize order-three element of G_x0")
    # χ_M is the degree-196883 character, with 3B value 53.
    source_character = z.chi_G_x0()[0]
    if source_character != 53:
        raise RuntimeError("Monster selected element is not certified class 3B")
    V7 = MMV(7)
    vector_specs = [
        ("A",0,0), ("A",0,1), ("B",0,1), ("C",0,1),
        ("T",0,0), ("X",1,0), ("Y",1,0), ("Z",1,0)
    ]
    tested=[]
    nonzero=0
    for spec in vector_specs:
        v = V7(*spec)
        projected = select_zeta(v,z)
        if projected * z != 2 * projected:
            raise RuntimeError(f"phase projector not zeta equivariant for {spec}")
        if projected != 0 * v:
            nonzero += 1
        tested.append(list(spec))
    if not nonzero:
        raise RuntimeError("all tested vectors projected to zero; cannot certify phase carrier")
    return dict(status="actual_mmgroup_run",group_element="Monster 3B",
                selected_phase="zeta=2 mod 7",selected_central_word=G3_WORD,
                source_url=SOURCE_URL,source_sha256=hashlib.sha256(G3_WORD.encode()).hexdigest(),
                mmgroup_version=version("mmgroup"),observed_character=source_character,
                tested_basis_vectors=tested,nonzero_selected_samples=nonzero,
                whole_W_zeta_dimension_from_source=65610,
                E_generator_words_aligned=False,
                normalizer_generator_words_aligned=False,
                monster_to_JFine_T_computed=False)
if __name__=="__main__":
    print(json.dumps(run(),indent=2))
