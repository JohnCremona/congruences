from sage.all import ZZ, QQ, EllipticCurve, prime_range, prod, Set, cremona_optimal_curves, srange, next_prime, CremonaDatabase, polygen, legendre_symbol
from sage.schemes.elliptic_curves.isogeny_small_degree import Fricke_polynomial

F7 = Fricke_polynomial(7)
x = polygen(QQ)
F7=F7(x)

def isog_pol(E):
    return F7-x*E.j_invariant()

def isog_pol0(E):
    return [pol for pol,e in isog_pol(E).factor() if pol.degree()==7][0]

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
    to prove that the representations themselves are isomorphich
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
    if mu6>5000000:
        print("Curves {} and {}: testing ell up to {} mod {}".format(E1.label(),E2.label(),mu6,p))
    actual_mu6 = mu6
    if mu6>mumax:
        mu6 = mumax
    if verbose:
        print("Curves {} and {}: testing ell up to {} mod {}".format(E1.label(),E2.label(),mu6,p))
    N1N2 = N1*N2
    for ell in prime_range(mu6):
        #print("testing ell = {}".format(ell))
        a1 = E1.ap(ell)
        a2 = E2.ap(ell)
        if ell.divides(N1N2):
            if N1N2.valuation(ell)==1 and (a1*a2-(ell+1))%p:
                return False, (ell,a1,a2)
        else:
            if (a1-a2)%p:
                return False, (ell,a1,a2)
    if mu6<actual_mu6:
        print("Warning! for curves {} and {}, to test for isomorphic semisimplifications we should have tested ell mod {} up to {}, but we only tested up to {}".format(E1.label(),E2.label(),p,actual_mu6,mu6))
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
            report(res, info, p, E1.label(), E2.label())

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
    print("{} has only {} supersingular primes up to {}".format(e.label(),len(pp),maxp))
    return pp

# Hash-based congruence finder

def hash1(p,E,plist):
    h = [E.ap(ell)%p for ell in plist]
    return sum(ai*p**i for i,ai in enumerate(h))

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
            print lab
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

def old_test_irred(s):
    Elist = [EllipticCurve(lab) for lab in s]
    rhos = [E.galois_representation() for E in Elist]
    r = [rho.is_irreducible(7) for rho in rhos]
    if all(r):
        return True
    if not any(r):
        return False
    print("Set {} is mixed: {}".format(s,r))
    return None

def test_irred(s):
    return len(isog_pol(EllipticCurve(s[0])).roots())==0

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
    return [(E.label(),E.isogeny_degree(C[0])) for E in C]

def split_class(label):
    """given the label of one curve E in a 7-irreducible isogeny class,
    return the list of all labels of curves in that class, partitioned
    into 2 parts where those in the first part are m-isogenous to E
    with legendre(m,7)=+1 and those in the second part (which may be
    empty) are m-isogenous to E with legendre(m,7)=-1.

    """
    C = CDB.isogeny_class(label)
    isodict = {E.label():E.isogeny_degree(C[0]) for E in C}
    set1 = [lab for lab in isodict if legendre_symbol(isodict[lab],7)==+1]
    set2 = [lab for lab in isodict if legendre_symbol(isodict[lab],7)==-1]
    return [set1,set2]

import XE7
XE7 = reload(XE7)

def test7iso(lcl, verbose=0):
    #print(lcl)
    splits = [split_class(c) for c in lcl]
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
