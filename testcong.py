from sage.all import ZZ, QQ, EllipticCurve, prime_range, prod, Set, cremona_optimal_curves, srange, next_prime, CremonaDatabase, polygen, legendre_symbol, PolynomialRing, NumberField, SteinWatkinsAllData
from sage.schemes.elliptic_curves.isogeny_small_degree import Fricke_polynomial

import XE7
import importlib
try:
    XE7 = reload(XE7)
except:
    XE7 = importlib.reload(XE7)

F7 = Fricke_polynomial(7)
F5 = Fricke_polynomial(5)
x = polygen(QQ)
F7=F7(x)

def SW_label(E):
    return ".".join([str(E.conductor()), str(E.ainvs())])

def label(E):
    try:
        return E.label()
    except:
        return SW_label(E)

def isog_pol(E, p=7):
    return Fricke_polynomial(p)(x)-x*E.j_invariant()

def sagepol(paripol):
    return x.parent()(str(paripol))

CDB = CremonaDatabase()

# read a data file which contains on each line
#
# p label1 label2
#
# where p is a congruence prime and the labels are of two curves suspected to be congruent mod p
#
def read_cong(fname):
    for L in open(fname).readlines():
        p, lab1, lab2 = L.split()
        yield ZZ(p), EllipticCurve(lab1), EllipticCurve(lab2)

# Given elliptic curves E1 and E2 and a prime p, use Kraus's Prop. 4
# to determine whether or not E1[p] and E2[p] have isomorphic
# semisimplifications (ignoring whether a symplectic isomorphism
# exists).

def test_cong(p, E1, E2, mumax=5000000, semisimp=True, verbose=False):
    """mumax: only test a_l for l up to this even if the bound is
    greater, but then output a warning semisimp: if True, output True
    when the two reps have isomorphic semisimplifications, don't try
    to prove that the representations themselves are isomorphic
    (which is not fully implemented anyway in the reducible case).
    Note that proving that the semisimplfications are isomorphic only
    depends on the isogeny class, but the condition that the
    representations themselves are isomorphic depends in general on
    the specific curves in their classes.

    """
    N1 = E1.conductor()
    N2 = E2.conductor()
    E1, d = E1.minimal_quadratic_twist()
    if d!=1:
        E1orig = E1
        E2orig = E2
        N1orig = N1
        N2orig = N2
        E2 = E2.quadratic_twist(d)
        if verbose:
            print("Twisting by {} before testing congruence".format(d))
            print("Before twisting, conductors were {} and {}".format(N1,N2))
        N1 = E1.conductor()
        N2 = E2.conductor()
        if verbose:
            print("After  twisting, conductors are {} and {}".format(N1,N2))
        if N2>400000: # we have made E2 worse, so untwist
            if verbose:
                print("After twisting, E2 is not in the database, so we undo the twisting")
            E1 = E1orig
            E2 = E2orig
            N1 = N1orig
            N2 = N2orig

    S = N1.gcd(N2).support()
    S1 = [ell for ell in S if E1.has_split_multiplicative_reduction(ell) and  E2.has_nonsplit_multiplicative_reduction(ell)]
    S2 = [ell for ell in S if E2.has_split_multiplicative_reduction(ell) and  E1.has_nonsplit_multiplicative_reduction(ell)]
    S = S1+S2
    M = N1.lcm(N2) * prod(S,1)
    mu = M * prod([(ell+1)/ell for ell in M.support()])
    mu6 = ZZ(int(mu/6)) # rounds down
    if verbose and mu6>5000000:
        print("Curves {} and {}: testing ell up to {} mod {}".format(label(E1),label(E2),mu6,p))
    actual_mu6 = mu6
    if mu6>mumax:
        mu6 = mumax
    if verbose:
        print("Curves {} and {}: testing ell up to {} mod {}".format(label(E1),label(E2),mu6,p))
    N1N2 = N1*N2
    for ell in prime_range(mu6):
        #print("testing ell = {}".format(ell))
        if ell==p:
            continue
        a1 = E1.ap(ell)
        a2 = E2.ap(ell)
        if ell.divides(N1N2):
            if N1N2.valuation(ell)==1 and (a1*a2-(ell+1))%p:
                return False, (ell,a1,a2)
        else:
            if (a1-a2)%p:
                return False, (ell,a1,a2)
    if mu6<actual_mu6:
        print("Warning! for curves {} and {}, to test for isomorphic semisimplifications we should have tested ell mod {} up to {}, but we only tested up to {}".format(label(E1),label(E2),p,actual_mu6,mu6))
    if verbose:
        print("The two mod-{} representations have isomorphic semisimplifications".format(p))
    if semisimp:
        return True, "up to semisimplification"
    #rho1 = E1.galois_representation()
    #rho2 = E2.galois_representation()
    #if rho1.is_irreducible(p) and rho2.is_irreducible(p):
    n1 = len(E1.isogenies_prime_degree(p))
    n2 = len(E2.isogenies_prime_degree(p))
    if n1==n2==0:
        if verbose:
            print("Both mod-{} representations are irreducible, hence they are isomorphic".format(p))
        return True, "irreducible"
    if n1==n2 and n1>1:
        if verbose:
            print("Both mod-{} representations are completely reducible, hence they are isomorphic".format(p))
        return True, "completely reducible"
    if  n1!=n2:
        return False, "nn"
    # now n1==n2==1 and it is harder to tell
    rho1 = E1.galois_representation()
    rho2 = E2.galois_representation()
    im1 = rho1.image_type(p)
    im2 = rho2.image_type(p)
    if im1 != im2:
        return False, "im"
    # Now they have the same image type.  If they are semistable at p
    # then they are isomorphic (either both have p-torsion point or
    # neither does)
    if N1.valuation(p)<=1 and N2.valuation(p)<=1:
        return True, "ss"
    # Giving up....
    return False, "ss" # flag that we have only proved that the semisimplfications are isomorphic

def report(res, info, p, lab1, lab2):
    if not res:
        print("Congruence mod {} fails for {} and {}".format(p,lab1,lab2))
        if info=="ss":
            print(" (isomorphic up to semisimplication but both are reducible, not totally reducible: failed to prove or disprove!)")
        elif info=="nn":
            print(" (isomorphic up to semisimplication but with different number of stable lines, so not isomorphic)")
        elif info=="im":
            print(" (isomorphic up to semisimplication but with different image types, so not isomorphic)")
        else:
            print(" (not even isomorphic up to semisimplication: {} )".format(info))
    else:
        print("{} and {} are proved to be congruent mod {} ({})".format(lab1,lab2,p,info))

def test_file(f, verbose=False):
    dat = read_cong(f)
    for p, E1, E2 in dat:
        res, info = test_cong(p,E1,E2)
        if verbose or not res:
            report(res, info, p, label(E1), label(E2))

def list_j_pairs(f):
    dat = read_cong(f)
    paircounts = {}
    npall = np  = 0
    for p, E1, E2 in dat:
        npall += 1
        j1 = E1.j_invariant()
        j2 = E2.j_invariant()
        pair = Set([j1,j2])
        if pair in paircounts:
            print("Repeat of {}".format(pair))
            paircounts[pair] += 1
        else:
            print("New pair {}".format(pair))
            paircounts[pair] = 1
            np += 1
    print("{} pairs of curves read, of which {} distinct pairs of j-invariants with mutiplicities {}".format(npall,np,paircounts.values()))
    return paircounts

# Result to conductor 400000:
#
# p=17: 8 pairs of curves, 1 pair of j-invariants
# p=13: 150 pairs of curves, 19 pairs of j-invariants
# p=11: 635 pairs of curves, 89 pair of j-invariants
#
# p=7 to 10000 only: 987 pairs of curves, 432 distinct pairs of j-invariants
#

def test_conductor_pair(p,N1,N2):
    import sage.databases.cremona as c
    for E1 in cremona_optimal_curves([N1]):
        if N1==N2:
            cl1 = c.class_to_int(c.parse_cremona_label(E1.label())[1])
        else:
            cl1 = 0
        for E2 in cremona_optimal_curves([N2]):
            if N1==N2:
                cl2 = c.class_to_int(c.parse_cremona_label(E2.label())[1])
            else:
                cl2 = 0
            if N1!=N2 or cl2<cl1:
                res, info = test_cong(p,E1,E2)
                if res:
                    report(res,info,p,E1.label(),E2.label())

p25 = prime_range(100)
curve_lists = {}

def get_curves(N):
    global curve_lists
    if N in curve_lists:
        return curve_lists[N]
    import pymongo
    C = pymongo.MongoClient(host='m0.lmfdb.xyz')
    #C = pymongo.MongoClient(host='lmfdb.warwick.ac.uk', port=37010)
    C.admin.authenticate('lmfdb','lmfdb')
    curves = C.elliptic_curves.curves
    curve_lists[N] = CN = list(curves.find({'conductor':int(N), 'number':int(1)}, {'iso_nlabel':True, 'label':True, 'aplist':True, '_id':False}))
    return CN

def test2(N1,ap1,N2,ap2,p):
    N1N2 = N1*N2
    for pi,ap1i,ap2i in reversed(zip(p25,ap1,ap2)):
        if pi.divides(N1N2):
            continue
        if (ap1i-ap2i)%p!=0:
            return False
    return True

def find_cong_db(Nmin, Nmax, p, ofile=None, verbose=False):
    if ofile:
        ofile=open(ofile, mode='a')
    nc = 0
    for N in srange(Nmin,Nmax+1):
        if N%100==0:
            print(N)
        curves_N = get_curves(N)
        if curves_N:
            if verbose:
                print("N1 = {} ({} classes)".format(N,len(curves_N)))
            for M in srange(11,N+1):
            #for M in srange(11,42000):
                curves_M = get_curves(M)
                if curves_M and verbose:
                    pass; print("...N2 = {} ({} classes)".format(M,len(curves_M)))
                for c1 in curves_N:
                    ap1 = c1['aplist']
                    iso1 = c1['iso_nlabel']
                    lab1 = str(c1['label'])
                    curves2 = [c2 for c2 in curves_M if M<N or c2['iso_nlabel']<iso1]
                    curves2 = [c2 for c2 in curves2 if test2(N,ap1,M,c2['aplist'],p)]
                    for c2 in curves2:
                        lab2 = str(c2['label'])
                        print("Candidate for congruence mod {}: {} {}".format(p,lab1,lab2))
                        E1 = EllipticCurve(lab1)
                        E2 = EllipticCurve(lab2)
                        res, reason = test_cong(p,E1,E2)
                        report(res,reason,p,lab1,lab2)
                        if res:
                            nc += 1
                            if ofile:
                                ofile.write("{} {} {}\n".format(p,lab1,lab2))
    if ofile:
        ofile.close()
    print("{} pairs of congruent curves found".format(nc))

# cong7.11-10000:     987 pairs all checked iso semisimp
# cong7.10001-42000: 1335 pairs ditto
# cong7.42k-400k:    running (mumax=5*10^6 means some pairs not 100% rigorous).

#  NB This run only compares pairs with both conductors in this range
#  so will have missed pairs (N1,N2) with N1<42k, N1>42k.  The code
#  was fixed before starting 4 additional runs for the ranges
#  200k-250k, 25k-300k, 300k-350k, 350k-400k.  We stopped this run
#  after it passed 200k.

# So: for 42k<N<200k we need to additionally check N against all N'<42k.  Running this --> cong7.extra.  Done, 8209 more.

# 200000-250000 finished cong7.200k-250k (3725 pairs)
# 250000-300000 finished cong7.250k-300k (3124 pairs)
# 300000-350000 finished cong7.300k-350k (3436 pairs)
# 350000-400000 finished cong7.350k-400k (3098 pairs)

#   -- cong7.1-100k        (4294 lines) checked, see cong7.1-100k.warnings (234)
#   -- cong7.100k-200k     (3747 lines) checked, see cong7.100k-200k.warnings (641)
#   -- cong7.200k-250k     (3651 lines) checked, see cong7.200k-250k.warnings (670)
#   -- cong7.250k-300k     (3124 lines) checked, see cong7.250k-300k.warnings (564)
#   -- cong7.300k-350k     (3436 lines) checked, see cong7.300k-350k.warnings (964)
#   -- cong7.350k-400k     (3098 lines) checked, see cong7.350k-400k.warnings (760)

#      Total 21350 of which 3833 are not proved
#            +8209 in extra run
#           =29559
#
# Modular form check finds 22705 in findcong.7.1-400000

def ssp(e, nssp=5, maxp=10000000):
    pp=[]
    for p in prime_range(maxp):
        if e.is_supersingular(p):
            pp.append(p)
        if len(pp)==nssp:
            return pp
    print("{} has only {} supersingular primes up to {}".format(label(e),len(pp),maxp))
    return pp

# Hash-based congruence finder

def hash1(p,E,qlist):
    h = [E.ap(q)%p for q in qlist]
    return sum(ai*p**i for i,ai in enumerate(h))

def hash1many(plist,E,qlist):
    aqlist = [E.ap(q) for q in qlist]
    return dict([(p,sum((ai%p)*p**i for i,ai in enumerate(aqlist))) for p in plist])

def make_hash(p, N1, N2, np=20):
    plist = [next_prime(400000)]
    while len(plist)<np:
        plist.append(next_prime(plist[-1]))

    hashtab = {}
    nc = 0
    for E in cremona_optimal_curves(srange(N1,N2+1)):
        nc +=1
        h = hash1(p,E,plist)
        lab = E.label()
        if nc%1000==0:
            print(lab)
        #print("{} has hash = {}".format(lab,h))
        if h in hashtab:
            hashtab[h].append(lab)
            #print("new set {}".format(hashtab[h]))
        else:
            hashtab[h] = [lab]

    ns = 0
    for s in hashtab.values():
        if len(s)>1:
            ns += 1
            #print s
    print("{} sets of conjugate curves".format(ns))
    return hashtab

def EC_from_SW_label(lab):
    N, ainvs = lab.split(".")
    N = ZZ(N)
    E = EllipticCurve([ZZ(a) for a in ainvs[1:-1].split(",")])
    assert E.conductor()==N
    return N, E

def make_hash_SW(plist, N1=0, N2=999, nq=30, tate=False):
    """Here N1 and N2 are in [0..999] and refer to the batch number, where
    batch n has curves of conductor between n*10^5 and (n+1)*10^5

    plist is a list of primes so we can make several hash tables in parallel

    If tate=True then ignore curves unless ord_p(j(E))=-1
    """
    # Compute the first nq primes greater than the largest conductor:

    qlist = [next_prime((N2+1)*10**5)]
    while len(qlist)<nq:
        qlist.append(next_prime(qlist[-1]))

    # Initialize hash tables for each p:

    hashtabs = dict([(p,dict()) for p in plist])
    nc = 0
    for N in range(N1,N2+1):
      print("Batch {}".format(N))
      for dat in SteinWatkinsAllData(N):
        nc +=1
        NE = dat.conductor
        E = EllipticCurve(dat.curves[0][0])
        assert E.conductor()==NE
        if tate and all(E.j_invariant().valuation(p)>=0 for p in plist):
            continue
        lab = SW_label(E)
        if nc%10000==0:
            print(lab)
        # if nc>10000:
        #     break
        h = hash1many(plist,E,qlist)
        for p in plist:
            if tate and E.j_invariant().valuation(p)>=0:
                continue
            hp = h[p]
            if hp in hashtabs[p]:
                hashtabs[p][hp].append(lab)
                print("p={}, new set {}".format(p,hashtabs[p][hp]))
            else:
                hashtabs[p][hp] = [lab]

    ns = dict([(p,len([v for v in hashtabs[p].values() if len(v)>1])) for p in plist])
    for p in plist:
        print("p={}: {} nontrivial sets of congruent curves".format(p,ns[p]))
    return hashtabs

def old_test_irred(s, p=7):
    Elist = [EllipticCurve(lab) for lab in s]
    rhos = [E.galois_representation() for E in Elist]
    r = [rho.is_irreducible(p) for rho in rhos]
    if all(r):
        return True
    if not any(r):
        return False
    print("Set {} is mixed: {}".format(s,r))
    return None

def test_irred(s, p=7):
    return len(isog_pol(EllipticCurve(s[0]),p).roots())==0

def test_set(s, p=7, maxp=20000000):
    E1 = EllipticCurve(s[0])
    for t in s[1:]:
        E2 = EllipticCurve(t)
        res, info = test_cong(p,E1,E2,maxp)
        if not res:
            report(res,info,p,s[0],t)


def test_sets(ss, p=7, maxp=20000000):
    n=0
    for s in ss:
        n+=1
        if len(s)>4:
            print("testing a set of size {}".format(len(s)))
        test_set(s,p,maxp)
        if n%100==0:
            print("{} sets tested".format(n))

"""Using 20 primes we find 20207 sets of conjugate curves (36 minutes)

See the check below: 94 pairs are definitely not isomorphic

Using 30 primes find 20138 sets of conjugate curves (45 minutes).  Checking...OK, only one pair which were not iso (25921a1 and 78400gw1). In the set ['25921a1', '78400gw1', '336973z1', '336973ba1']
the first curve is *not* isomorphic to the other 3 so this set should be just ['78400gw1', '336973z1', '336973ba1']


isom_sets holds 20138 sets of size at least 2 of (isogeny classes) or probably isomorphic sets of curves

{2: 18420,
 3: 1364,
 4: 277,
 5: 32,
 6: 5,
 7: 7,
 8: 5,
 9: 4,
 10: 6,
 11: 3,
 13: 1,
 14: 1,
 16: 2,
 18: 2,
 19: 4,
 32: 1,
 35: 1,
 36: 1,
 45: 1,
 76: 1}

Of these, 19883 are irreducible and 255 reducible, in isom_sets_irred and isom_sets_red

Run Kraus on all the 255 reducible sets (with max prime 20000000): done, all proved isomorphic up to ss except the bogus one:

Congruence mod 7 fails for 25921a1 and 78400gw1
 (not even isomorphic up to semisimplication: (11, 4, -4) )

This is for set ['25921a1', '78400gw1', '336973z1', '336973ba1'] where the last 3 are isomorphic, the first one is not.

Run Kraus on all the 19883 irreducible sets (with max prime 20000000): running...done.  All proved except

Curves 237282i1 and 292982b1: testing ell up to 21212928 mod 7
Warning! for curves 237282i1 and 292982b1, to test for isomorphic
semisimplifications we should have tested ell mod 7 up to 21212928,
but we only tested up to 20000000

-- a second run on just this pair finishes proving that all 20138 sets are definitely isomorphic up to ss.

Code to run:
hashtab7_30 = make_hash(7,11,400000,30)

for s in hashtab7_30.values():
     if len(s)>1:
         E1 = EllipticCurve(s[0])
         for r in s[1:]:
             E2 = EllipticCurve(r)
             res, info = test_cong(7,E1,E2)
             if not res:
                 report(res,info,7,s[0],r)


isom_sets = [s for s in hashtab7_30.values() if len(s)>1]
len(isom_sets)
res = [test_irred(s) for s in isom_sets]
isom_sets_irred = [s for s in isom_sets if test_irred(s)]
len(isom_sets_irred)
isom_sets_red = [s for s in isom_sets if not s in isom_sets_irred]
len(isom_sets_red)
len(isom_sets_irred)
red_out = open("cong7red.txt",'w')
for s in isom_sets_red:
    red_out.write( " ".join(s) + "\n")
red_out.close()
irred_out = open("cong7irred.txt",'w')
for s in isom_sets_irred:
    irred_out.write( " ".join(s) + "\n")
irred_out.close()
redsets = [[(l,EllipticCurve(l).galois_representation().reducible_primes()) for l in s] for s in isom_sets_red]
redsets27 = [r for r in redsets if any(2 in ri[1] for ri in r)]
redsets37 = [r for r in redsets if any(3 in ri[1] for ri in r)]
redsets7 = [r for r in redsets if all([7]== ri[1] for ri in r)]
irredsets = [[(l,EllipticCurve(l).galois_representation().reducible_primes()) for l in s] for s in isom_sets_irred]
irredsets_nontriv = [r for r in irredsets if any(ri[1]!=[] for ri in r)]

## Mod 17 computation:
# 10 primes no good (29m)
%time hashtab17_10 = make_hash(17,11,400000,10)
len([s for s in hashtab17_10.values() if len(s)>1])
1673
# 20 primes?
%time hashtab17_20 = make_hash(17,11,400000,20)
len([s for s in hashtab17_20.values() if len(s)>1])
26
# 30 primes?
%time hashtab17_30 = make_hash(17,11,400000,30)
len([s for s in hashtab17_30.values() if len(s)>1])
9
[s for s in hashtab17_30.values() if len(s)>1]
[['3675k1', '47775cq1'],
 ['3675g1', '47775bf1'],
 ['3675o1', '47775da1'],
 ['11025r1', '143325et1'],
 ['11025bm1', '143325ba1'],
 ['3675b1', '47775b1'],
 ['25921a1', '78400gw1'],   <-------- bogus
 ['11025w1', '143325ej1'],
 ['11025bi1', '143325be1']]
"""

def all_c(label):
    """given the label of one curve in an isogeny class, return the list
    of all labels of curves in that class.
    """
    C = CDB.isogeny_class(label)
    return [(label(E),E.isogeny_degree(C[0])) for E in C]

def split_class(label, p):
    """given the label of one curve E in a p-irreducible isogeny class,
    return the list of all labels of curves in that class, partitioned
    into 2 parts where those in the first part are m-isogenous to E
    with legendre(m,p)=+1 and those in the second part (which may be
    empty) are m-isogenous to E with legendre(m,p)=-1.
    """
    C = CDB.isogeny_class(label)
    isodict = {label(E):E.isogeny_degree(C[0]) for E in C}
    set1 = [lab for lab in isodict if legendre_symbol(isodict[lab],7)==+1]
    set2 = [lab for lab in isodict if legendre_symbol(isodict[lab],7)==-1]
    return [set1,set2]

def split_class_red(label, p, ignore_symplectic=False):
    """given the label of one curve E in a p-reducible isogeny class,
    return the list of all labels of curves E' in that class,
    partitioned into 4 parts (or 2 if ignore_symplectic==True),
    according to the degree m of the isogeny from E to E' as follows:

    0: legendre(m,p)=+1
    1: legendre(m,p)=-1
    2: p|m and legendre(m/p,p)=+1
    3: p|m and legendre(m/p,p)=-1

    When ignore_symplectic==True, parts 0&1 and 2&3 are joined.

    Assumption:  p>=7 so no p^2-isogenies exist.

    If there are no p-isogenies this will still work, but parts 2,3
    will be empty.  Curves within each part are symplectically
    isomorphic; between parts 0 and 1 and between parts 2 and 3, they
    are anti-symplectically isomorphic.  All curves in the class have
    isomorphic semisimplfications of the mod-p representations.  There
    are no mod-p isomorphisms between parts 0,1 and parts 2,3 since
    the two characters which form the common semisimplfication are
    distinct (since the determinant of the mod-p representation is
    surjective, its values cannot all be squares mod p) and isogenies
    of degree divisible by 7 swap the two characters.

    For p=7, parts 0 and 2 will contain either 1 or 2 curves each
    depending on whether the class admits 2-isogenies.  Parts 1 and 3
    will be empty unless the class admits 3-isogenies, in which case
    all four parts will contain a single label.  This is because of
    the classification of isogeny classes over Q: when there are
    7-isogenies then the class size is 2 or 4 and in the latter case
    there are 2- or 3-isogenies but not both.

    Examples:

    Class 26b:    (26b1) --7-- (26b2)

    With ignore_symplectic==False:
    [['26b1'], [], ['26b2'], []]

    With ignore_symplectic==True:
    [['26b1'], ['26b2']]

    Class 49a:    (49a1) --2-- (49a2)
                     |            |
                     7            7
                     |            |
                  (49a3) --2-- (49a4)

    With ignore_symplectic==False:
    [['49a2', '49a1'], [], ['49a4', '49a3'], []]

    With ignore_symplectic==True:
    [['49a2', '49a1'], ['49a4', '49a3']]

    Class 162b:   (162b1) --3-- (162b2)
                     |            |
                     7            7
                     |            |
                  (162b4) --3-- (162b3)

    With ignore_symplectic==False:
    [['162b1'], ['162b2'], ['162b3'], ['162b4']]

    With ignore_symplectic==True:
    [['162b1', '162b2'], ['162b3', '162b4']]

    """
    C = CDB.isogeny_class(label)
    isodict = {label(E):E.isogeny_degree(C[0]) for E in C}
    def t(m):
        if p.divides(m):
            return 2 + (1-legendre_symbol(m//p,p))//2
        else:
            return (1-legendre_symbol(m,p))//2
    sets = [[] for _ in range(4)]
    for lab in isodict:
        sets[t(isodict[lab])].append(lab)
    return sets

def test7iso(lcl, verbose=0):
    """Given a list of at least 2 isogeny class labels of curves whose mod
    7 representations are irreducible and isomorphic, returns a list
    of two lists of curve labels, together containing all curves in
    all the isogeny classes, such that the curves in each sublist are
    symplectically isomorphich while between sublists they are
    antisymplectically isomorphic.
    """
    #print(lcl)
    splits = [split_class(c,7) for c in lcl]
    symplectics = splits[0][0]
    antisymplectics = []
    lab = symplectics[0]
    if verbose:
        print("base curve {} in set {}".format(lab, lcl))
    X = XE7.XE7.from_label(lab)

    for cl in splits:
        if verbose>1:
            print("class = {}".format(cl))
        for part in cl:
            if len(part)==0:
                continue
            if verbose>1:
                print("part-class = {}".format(part))
            lab1 = part[0]
            if lab1==lab:
                continue
            if verbose>1:
                print("lifting j of  curve {}".format(lab1))
            res = X.lift_curve(EllipticCurve(lab1))
            if res==None:
                antisymplectics += part
            else:
                symplectics += part
    return [symplectics,antisymplectics]

def isogeny_kernel_field(phi, optimize=False):
    pol = phi.kernel_polynomial()
    Fx = pol.splitting_field('b',degree_multiple=pol.degree(), simplify_all=True)
    xP=pol.roots(Fx)[0][0]
    yP=phi.domain().lift_x(xP, extend=True)[1]
    Fxy = yP.parent()
    Fxy = Fxy.absolute_field('c')
    if optimize:
        Fxy = Fxy.optimized_representation()[0]
    return Fxy

def isogeny_star_field(phi, optimize=True):
    p = phi.degree()
    F_pol = Fricke_polynomial(p)
    t = F_pol.parent().gen()
    star_pol = F_pol-t*phi.domain().j_invariant()
    star_pol = (f for f,e in star_pol.factor() if f.degree()==p).next()
    assert star_pol.is_irreducible()
    F = NumberField(star_pol, 's')
    if optimize:
        F = F.optimized_representation()[0]
    return F

def test_field_iso(pol1, pol2):
    if pol1 == pol2:
        return True
    if pol1.degree()!=pol2.degree():
        return False
    assert pol1.is_irreducible() and pol2.is_irreducible()
    res =  0 < len(pol1.change_ring(PolynomialRing(NumberField(pol2,'b'),'y')).roots())
    #print("testing isomorphism of {} and {}: {}".format(pol1,pol2, res))
    return res

def mod_p_iso_red(E1, E2, p, verbose=True):
    """Given curves E1, E2 whose mod-p representations are reducible and
    isomorphic up to semisimplification, with p-isogenous curves E1'
    and E2' respectively (uniquely determined if we assume p>=7),
    return a list of pairs of curves from {E1,E1',E2,E2'} whose mod-p
    representations are actually isomorphic.

    Since E1 and E1' do not have isomorphic mod-p representations and
    neither do E2, E2', the possible outputs are (with labels instead
    of E1, E2 etc):

    []
    [(E1,E2)]
    [(E1,E2')]
    [(E1',E2)]
    [(E1',E2')]
    [(E1,E2), (E1',E2')]
    [(E1,E2'), (E1',E2)]

    No examples have yet been encountered of the double isomorphisms
    (the last two lines above) so if one occurs a prominent message is
    displayed.

    Method: (1) Compute E1' and E2' and the four 7-isogenies between
    these (including duals).  (2) Compute the kernel fields of the
    four isogeny characters, and hence set (E3,E3')=(E2,E2') or
    (E2',E2) so that the two characters for E1,E3 and for E1',E3' are
    in the same order.  (3) Compute the "star-fields" of degree p for
    each curve to detect isomorphisms when these coincide.

    """
    if verbose:
        print("testing E1[{}]=E2[{}] for E1={}, E2={}".format(p,p,E1.ainvs(),E2.ainvs()))

    flip = False

    phi1 = E1.isogenies_prime_degree(p)[0]
    phi1hat = phi1.dual()
    E1dash = phi1.codomain()
    phi2 = E2.isogenies_prime_degree(p)[0]
    phi2hat = phi2.dual()
    E2dash = phi2.codomain()

    F1, F2 = [isogeny_kernel_field(phi) for phi in [phi1,phi2]]
    F1dash, F2dash = [isogeny_kernel_field(phi) for phi in [phi1hat,phi2hat]]
    if F1==F2 or F1.is_isomorphic(F2):
        if verbose:
            print("isogeny characters agree, splitting field of isogeny character is {}".format(F1))
    else:
        if verbose:
            print("isogeny characters do not agree, flipping E2")
        if F1==F2dash or F1.is_isomorphic(F2dash):
            flip = True
            if verbose:
                print("isogeny characters agree after flipping E2, splitting field of isogeny character is {}".format(F1))
        else:
            print("Warning in mod_p_iso_red: the mod-{} representations of curves {} and {} do not have isomorphic semisimplifications".format(p,E1.ainvs(),E2.ainvs()))
            return 0

    E3,   E3dash  = (E2dash,E2)    if flip else (E2,E2dash)
    phi3, phi3hat = (phi2hat,phi2) if flip else (phi2,phi2hat)

    # Now the ordered pair of isogeny characters of E1 and E3 are
    # equal as are those of E1dash and E3dash.  Next we compare E1, E3
    # to see if they have the same * and also compare E1dash, E3dash
    # to see if they do (which is not equivalent).
    if verbose:
        print("continuing with test of * components")
    star_field1 = isogeny_star_field(phi1)
    star_field3 = isogeny_star_field(phi3)
    res1 =  star_field1.is_isomorphic(star_field3)          # True iff E1[p] and E3[p] are isomorphic
    star_field1dash = isogeny_star_field(phi1hat)
    star_field3dash = isogeny_star_field(phi3hat)
    res2 =  star_field1dash.is_isomorphic(star_field3dash)  # True iff E1'[p] and E3'[p] are isomorphic

    # return a list of up to 2 isomorphic pairs
    isopairs = []
    if res1:
        isopairs.append((label(E1),label(E3)))
    if res2:
        isopairs.append((label(E1dash),label(E3dash)))
    if res1 and res2:
        print("**********double isomorphism between ({},{}) and ({},{})".format(label(E1),label(E3),(label(E1dash),label(E3dash))))
    return isopairs

    # # return a 4-tuple comparing (E1,E2), (E1, E2'), (E1',E2), (E1',E2')
    # if flip:
    #     return [False , res1, res2, False]
    # else:
    #     return [res1, False, False, res2]

def mod_p_iso_red_labels(lab1, lab2, p, verbose=True):
    """Given labels lab1, lab2 of non-isogenous curves whose mod-p
    representations are reducible and isomorphic up to
    semisimplification: return the same as mod_p_iso_red for the
    curves with these labels.
    """
    return mod_p_iso_red(EllipticCurve(lab1), EllipticCurve(lab2),p,verbose)

def mod_p_iso_red_set(ss, p=7, Detail=0):
    """Given a list of labels of non-isogenous curves whose mod-p
    representations are reducible and isomorphic up to
    semisimplification, return a list of disjoint lists of labels
    whose union is the list of all curves isogenous to the input
    curves, such that the curves have isomorphic mod-p representations
    if and only if they are in the same sublist.
    """
    if Detail>1:
        print("testing {}".format(ss))
    nss = len(ss)

    base_curves = [EllipticCurve(lab) for lab in ss]
    isogenies = [E.isogenies_prime_degree(p)[0] for E in base_curves]
    isog_curves = [phi.codomain() for phi in isogenies]

    kernel_field = isogeny_kernel_field(isogenies[0], optimize=True)
    dual_kernel_field = isogeny_kernel_field(isogenies[0].dual(), optimize=True)
    if Detail>1:
        print("Kernel field:      {}".format(kernel_field))
        print("Dual kernel field: {}".format(dual_kernel_field))

    # Swap the two parts in each class after the first, if necessary,
    # so that the isogeny characters of the curves in all the first
    # parts agree.

    for i, E, phi, Edash in zip(range(nss), base_curves, isogenies, isog_curves):
        this_kernel_field = isogeny_kernel_field(phi, optimize=True)
        if not this_kernel_field.is_isomorphic(kernel_field):
            if this_kernel_field.is_isomorphic(dual_kernel_field):
                if Detail>1:
                    print("swapping {}!".format(i))
                base_curves[i] = Edash
                isog_curves[i] = E
                phi = isogenies[i] = phi.dual()
            else:
                print("problem at i={}: this kernel field = {}, different from both the kernel field and dual kernel field!".format(i,this_kernel_field))

    if Detail>1:
        print("After sorting, base curves are {}".format([label(E) for E in base_curves]))
        print("  and {}-isogenous curves are {}".format(p, [label(E) for E in isog_curves]))

    # Now the curves in base_curves have the same isogeny characters
    # in the same order, and we sort them according to their *-fields:
    star_fields = [isogeny_star_field(psi) for psi in isogenies]
    maps = dict([(F,[label(E) for E,F1 in zip(base_curves,star_fields) if F1.is_isomorphic(F)]) for F in star_fields])
    if Detail:
        print("star field subsets: {}".format(maps.values()))
    isog_star_fields = [isogeny_star_field(psi.dual()) for psi in isogenies]
    isog_maps = dict([(F,[label(E) for E,F1 in zip(isog_curves,isog_star_fields) if F1.is_isomorphic(F)]) for F in isog_star_fields])
    if Detail:
        print("star-star field subsets: {}".format(isog_maps.values()))
    return maps.values(), isog_maps.values()
    #return [label(E) for E in base_curves], [label(E) for E in isog_curves]

#['19327077.(0, 0, 1, 502002, 31437875)', '96635385.(0, 0, 1, 136711878, 321000500520)']

def process_tate_set(p, data, plim=10000):
    print("processing a set of {} curves for p={}".format(len(data),p))
    res = []
    curves = [EC_from_SW_label(lab)[1] for lab in data]
    pr_curves = [E for E in curves if E.j_invariant().valuation(p) %p ==0]
    nprc = len(pr_curves)
    print("Of those, {} are peu ramifie".format(len(pr_curves)))
    if nprc<2:
        print("no interesting pairs")
        return []
    print("The {} peu ramifie curves are {}".format(len(pr_curves), [E.ainvs() for E in pr_curves]))
    print([[test_cong(7,E1,E2,plim) for E2 in curves[i+1:]] for i,E1 in enumerate(curves)])
    return pr_curves

