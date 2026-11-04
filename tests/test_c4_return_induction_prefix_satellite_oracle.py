"""Independent literal-word oracle for C4 return-induction negative control.

Source: docs/c4-return-induction-prefix-satellite-counterexample-2026-11-04.md
The return words are DISCOVERED from the fixed-point prefix before comparison
with the paper list. Python is independent of the canonical Mojo implementation.
The unbounded claim follows from the prefix-code lemma, not bounded checking.
"""


SOURCE = ("01", "121", "012")
EXPECTED_RETURNS = ("01121121", "012121121", "012121", "01121")
EXPECTED_INDUCED = ("012", "3212", "322", "02")


def expand(sub, word, power=1):
    if power < 0 or power > 8:
        raise ValueError("explicit exact-word oracle power budget")
    for _ in range(power):
        if len(word) > 100_000:
            raise ValueError("over exact-word materialization budget")
        word = "".join(sub[int(c)] for c in word)
    return word


def split_at_zero(word):
    if not word or word[0] != "0" or any(c not in "012" for c in word):
        raise ValueError("no initial marker or malformed physical word")
    offsets = [i for i,c in enumerate(word) if c == "0"]
    return [word[a:b] for a,b in zip(offsets, offsets[1:]+[len(word)])]


def return_words_from_prefix(source, level=6):
    # Do not supply any precomputed return words to the discovery pass.
    w = expand(source, "0", level)
    pos = [i for i,c in enumerate(w) if c=="0"]
    complete = [w[start:end] for start,end in zip(pos,pos[1:])]
    return tuple(dict.fromkeys(complete)), complete


def derive_return_substitution(source, words):
    if len(words)!=len(set(words)) or not words:
        raise ValueError("duplicate or empty return alphabet")
    if any(not w.startswith("0") or w.count("0")!=1 or
           any(c not in "012" for c in w) for w in words):
        raise ValueError("invalid marker return word")
    lookup={w:str(i) for i,w in enumerate(words)}
    induced=[]
    for w in words:
        physical=expand(source,w)
        pieces=split_at_zero(physical)
        if any(part not in lookup for part in pieces):
            raise ValueError("supplied return set is not closed")
        letters="".join(lookup[part] for part in pieces)
        assert "".join(words[int(i)] for i in letters)==physical
        induced.append(letters)
    return tuple(induced)


def count_prefix(w,p):
    return tuple(w[:p].count(str(i)) for i in range(3))


def first_return_prefix(source):
    w=expand(source,"0",3)
    parts=split_at_zero(w)
    if len(parts)<2:
        raise AssertionError("insufficient second zero")
    return parts[0],w


def incidence(sub):
    return [[w.count(str(i)) for w in sub] for i in range(len(sub))]


def matmul(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(A)))
             for j in range(len(B))] for i in range(len(A))]


def is_prefix_free(words):
    return all(not x.startswith(y) and not y.startswith(x)
               for i,x in enumerate(words)
               for j,y in enumerate(words) if i<j)


def test_discover_actual_four_return_words_without_hardcoded_discovery():
    discovered, complete=return_words_from_prefix(SOURCE,6)
    assert discovered==EXPECTED_RETURNS
    assert all(r.count("0")==1 and r.startswith("0") for r in discovered)
    assert all(r in complete for r in EXPECTED_RETURNS)
    first,third=first_return_prefix(SOURCE)
    assert first==EXPECTED_RETURNS[0]
    assert third=="01121121012121"
    assert complete[:4] == list(EXPECTED_RETURNS)
    assert derive_return_substitution(SOURCE,discovered)==EXPECTED_INDUCED


def test_every_return_image_is_an_ordered_complete_literal_factorization():
    # Build each codeword from actual physical substitution of each discovered
    # return, rather than from expected tau strings.
    R,_=return_words_from_prefix(SOURCE,6)
    tau=derive_return_substitution(SOURCE,R)
    assert tau==EXPECTED_INDUCED
    assert [split_at_zero(expand(SOURCE,r)) for r in R]==[
        [R[0],R[1],R[2]],
        [R[3],R[2],R[1],R[2]],
        [R[3],R[2],R[2]],
        [R[0],R[2]],
    ]
    for i,r in enumerate(R):
        assert expand(SOURCE,r)=="".join(R[int(j)] for j in tau[i])
    # Intertwining on nontrivial concatenations, independently decoded.
    for code in ("0","1","2","3","0123","3201"):
        real="".join(R[int(i)] for i in code)
        left=expand(SOURCE,real)
        right="".join(R[int(i)] for i in expand(tau,code))
        assert left==right


def test_induced_four_letter_substitution_is_primitive():
    M=incidence(EXPECTED_INDUCED)
    assert M==[[1,0,0,1],[1,1,0,0],[1,2,2,1],[0,1,1,0]]
    cube=matmul(matmul(M,M),M)
    assert cube==[[3,4,3,2],[3,2,1,2],[17,20,13,10],[7,8,5,4]]
    assert all(x>0 for row in cube for x in row)


def test_genuine_source_strong_coincidence_and_prefix_satellite():
    assert SOURCE[2] == SOURCE[0]+"2"
    w=[expand(SOURCE,str(i),2) for i in range(3)]
    assert w==["01121","121012121","01121012"]
    assert all(word[4]=="1" and count_prefix(word,4)==(1,2,1)
               for word in w)
    for n in range(1,7):
        assert expand(SOURCE,"2",n)==(
            expand(SOURCE,"0",n)+expand(SOURCE,"2",n-1)
        )


def test_return_images_are_prefix_free_and_remain_so_all_checked_powers():
    R,_=return_words_from_prefix(SOURCE,6)
    tau=derive_return_substitution(SOURCE,R)
    assert is_prefix_free(tau)
    assert R[0].startswith(R[3]) and R[1].startswith(R[2])
    # The physical return words themselves are NOT a prefix code.
    assert not is_prefix_free(R)
    for n in range(1,7):
        expanded=tuple(expand(tau,str(i),n) for i in range(4))
        assert is_prefix_free(expanded)
        # Any derived image code is decoded to exactly the original
        # nth physical iterate of its starting return word.
        for i in range(4):
            decoded="".join(R[int(j)] for j in expanded[i])
            assert decoded==expand(SOURCE,R[i],n)


def test_prefix_free_lemma_first_differing_letter_controls():
    # Positive and negative controls for the *general* combinatorial lemma.
    examples=(
        ("01","02","12"),
        ("012","3212","322","02"),
        ("0","10","11"),
    )
    for theta in examples:
        assert is_prefix_free(theta)
        for n in range(1,6):
            img=[expand(theta,str(i),n) for i in range(len(theta))]
            assert is_prefix_free(img)
    assert not is_prefix_free(("0","01"))
    assert not is_prefix_free(("10","10"))


def test_incomplete_or_malformed_return_inventory_fails_closed():
    R,_=return_words_from_prefix(SOURCE,6)
    for candidate in (
        R[:3],
        (R[0],R[0],R[2],R[3]),
        ("0102",)+R[1:],
        ("",)+R[1:],
    ):
        try:
            derive_return_substitution(SOURCE,candidate)
        except ValueError:
            continue
        raise AssertionError(("bad return inventory accepted",candidate))


def test_zero_return_induction_not_automatically_prefix_satellite():
    R,_=return_words_from_prefix(SOURCE,6)
    tau=derive_return_substitution(SOURCE,R)
    assert SOURCE[2].startswith(SOURCE[0])
    for i in range(len(tau)):
        for j in range(i+1,len(tau)):
            assert not tau[i].startswith(tau[j])
            assert not tau[j].startswith(tau[i])
    # This is an exact algebraic counterexample to the proposed shortcut,
    # not a negative result about strong coincidence or general C4.


def test_exact_common_expanding_residual_for_both_return_pairings():
    R,_=return_words_from_prefix(SOURCE,6)
    tau=derive_return_substitution(SOURCE,R)
    B=SOURCE[1]
    assert (R[0],R[1]) == (R[3]+B,R[2]+B)
    lengths=[]
    for n in range(0,7):
        tail=expand(SOURCE,"1",n+1)
        assert expand(SOURCE,R[0],n)==expand(SOURCE,R[3],n)+tail
        assert expand(SOURCE,R[1],n)==expand(SOURCE,R[2],n)+tail
        lengths.append(len(tail))
        if n:
            assert len(tail)>lengths[-2]
            # The physical prefixes continue to compare while their
            # derived-code images at EVERY positive power do not.
            code=tuple(expand(tau,str(i),n) for i in range(4))
            assert not code[0].startswith(code[3])
            assert not code[1].startswith(code[2])
    assert lengths==[3,9,26,74,210,596,1692]


def test_full_rank_parikh_intertwining_and_null_eigen_direction():
    R,_=return_words_from_prefix(SOURCE,6)
    tau=derive_return_substitution(SOURCE,R)
    M=incidence(SOURCE)
    N=incidence(tau)
    P=[[w.count(str(i)) for w in R] for i in range(3)]
    assert P==[[1,1,1,1],[5,5,3,3],[2,3,2,1]]
    assert matmul(M,P)==matmul(P,N)==[
        [3,4,3,2],[13,14,9,8],[7,8,5,4]
    ]
    (a,b,c),(d,e,f),(g,h,i)=[row[:3] for row in P]
    determinant=a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
    assert determinant==2  # rank P = 3, nontrivial 1-d kernel
    v=(-1,1,-1,1)
    assert all(sum(P[i][j]*v[j] for j in range(4))==0
               for i in range(3))
    assert all(sum(N[i][j]*v[j] for j in range(4))==0
               for i in range(4))
    # The char polynomial consequence x * chi_M(x) is proved using
    # quotient action and rank. A finite direct determinant check
    # at five integer arguments independently catches coefficient drift.
    def determinant_integer(A):
        if len(A)==1:
            return A[0][0]
        return sum((-1 if j%2 else 1)*A[0][j]*
                   determinant_integer([row[:j]+row[j+1:] for row in A[1:]])
                   for j in range(len(A)))
    for x in (-2,-1,0,1,2,3,4):
        f=x**3-4*x*x+4*x-2
        A=[[x*int(i==j)-N[i][j] for j in range(4)] for i in range(4)]
        assert determinant_integer(A)==x*f
