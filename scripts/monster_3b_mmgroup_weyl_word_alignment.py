#!/usr/bin/env python3
"""Fail-closed actual Monster-E word alignment (no synthetic generator fallback).

Consumes a source-attributed JSON manifest with keys:
 center_word, translation_words[6], modulation_words[6], source_url,
 optionally normalizer_lifts: [{name,word,central_image:1|-1,
     translation_images:[{a:[6],b:[6],t:int}], modulation_images:[...]}].
This is a *real* MM group-element check, not a character-table or numerical
coincidence. It does not claim a W_zeta<->JFine vector intertwiner until a
separate source-coordinate basis is constructed and its matrices are checked.

Primary sources: Barraclough thesis (2005) §5.3; Bray-Wilson (2006);
Martin Seysen, mmgroup; original source-specific words must be attributed in
the manifest. Reuse DASHI/Moonshine/Monster3BFiniteHeisenbergCentralExtensionExact
for group laws rather than creating a second theorem owner.
"""
import argparse
import hashlib
import json
from pathlib import Path

def check_words(obj):
    from mmgroup import MM
    if not isinstance(obj,dict):
        raise ValueError("manifest root must be an object")
    source = obj.get("source_url")
    if not isinstance(source,str) or not source.strip():
        raise ValueError("source_url required: no unattributed generator lists")
    zword = obj.get("center_word")
    Awords = obj.get("translation_words")
    Bwords = obj.get("modulation_words")
    if not isinstance(zword,str) or not zword:
        raise ValueError("center_word required")
    if not isinstance(Awords,list) or len(Awords)!=6 or not all(isinstance(w,str) and w for w in Awords):
        raise ValueError("exactly six literal translation_words required")
    if not isinstance(Bwords,list) or len(Bwords)!=6 or not all(isinstance(w,str) and w for w in Bwords):
        raise ValueError("exactly six literal modulation_words required")
    z,A,B=MM(zword),[MM(w) for w in Awords],[MM(w) for w in Bwords]
    one=z**0
    if z.order()!=3:
        raise ValueError("centre does not have order 3")
    if not z.in_G_x0() or z.chi_G_x0()[0]!=53:
        raise ValueError("literal centre not in certified Monster 3B class")
    allgens=A+B
    for i,g in enumerate(allgens):
        if g.order()!=3:
            raise ValueError(f"Weyl generator {i} not of order 3")
        if z*g != g*z:
            raise ValueError(f"Weyl generator {i} does not centralize z")
    for i in range(6):
        for j in range(6):
            if A[i]*A[j]!=A[j]*A[i]:
                raise ValueError(f"translations {i},{j} do not commute")
            if B[i]*B[j]!=B[j]*B[i]:
                raise ValueError(f"modulations {i},{j} do not commute")
            expected=(z if i==j else one)*A[j]*B[i]
            if B[i]*A[j]!=expected:
                raise ValueError(f"Weyl pair ({i},{j}) has wrong central phase")

    def word_for_coordinate(d):
        if not isinstance(d,dict):raise ValueError("normalizer image must be dict")
        a,b,t=d.get("a"),d.get("b"),d.get("t")
        if not (isinstance(a,list) and isinstance(b,list) and len(a)==6 and len(b)==6
                and all(type(v) is int and 0<=v<3 for v in a+b)
                and type(t) is int and 0<=t<3):
            raise ValueError("normalizer image must have ternary a[6], b[6], t")
        g=one
        for i,v in enumerate(a):g=g*A[i]**v
        for i,v in enumerate(b):g=g*B[i]**v
        return g*z**t
    normalizer_results=[]
    for n in obj.get("normalizer_lifts",[]):
        if not isinstance(n,dict) or not isinstance(n.get("word"),str):
            raise ValueError("normalizer lift needs a source-defined word")
        h=MM(n["word"])
        sign=n.get("central_image")
        if sign not in (1,-1) or type(sign) is not int:
            raise ValueError("normalizer central_image must be 1 or -1")
        if h*z*h**(-1)!=z**sign:
            raise ValueError(f"normalizer lift {n.get('name')} has wrong central inversion")
        for family,generators,key in (("A",A,"translation_images"),("B",B,"modulation_images")):
            images=n.get(key)
            if not isinstance(images,list) or len(images)!=6:
                raise ValueError(f"normalizer {family} images require 6 explicit E coordinates")
            for i,g in enumerate(generators):
                if h*g*h**(-1)!=word_for_coordinate(images[i]):
                    raise ValueError(f"normalizer {n.get('name')}: {family}[{i}] not same E")
        normalizer_results.append({"name":n.get("name","unnamed"),"central_image":sign,
                                   "all_twelve_generator_images_verified":True})
    data=json.dumps(obj,sort_keys=True,separators=(',',':')).encode()
    return dict(status="verified_actual_MM_word_relations",source_url=source,
                manifest_sha256=hashlib.sha256(data).hexdigest(),
                central_class="Monster 3B",number_of_weyl_generators=12,
                central_weyl_relations_checked=36,translation_relations_checked=36,
                modulation_relations_checked=36,
                normalizer_lifts=normalizer_results,
                actual_Wzeta_basis_intertwiner_constructed=False,
                source_character_12_plus_78_transported=False)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("manifest",type=Path,help="existing source-aligned MM word manifest")
    p.add_argument("--receipt",type=Path,help="output JSON only upon successful verification")
    args=p.parse_args()
    if not args.manifest.is_file():
        p.error("manifest file missing; a character table is NOT a word manifest")
    data=json.loads(args.manifest.read_text())
    try:
        from mmgroup import MM
    except ImportError as exc:
        p.error("mmgroup not installed; cannot inspect actual Monster element words")
    result=check_words(data)
    encoded=json.dumps(result,indent=2)+"\n"
    if args.receipt:
        args.receipt.write_text(encoded)
    print(encoded,end="")

if __name__=="__main__":
    main()
