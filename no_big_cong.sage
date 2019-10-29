# Code for testing the Frey-Mazur conjecture on the database

def test_cong(E1,E2, m_max=17, p_max=1000):
    """
    Return False if there is no mod-p congruence between E1 and E2 for any p>M_max.
    Return True, p, d if there appears to be a mod-d congruence for some d>m_max, having only checked primes up to p.
    """
    d = 0
    for p in Primes():
        if p.divides(E1.conductor()) or p.divides(E2.conductor()):
            continue
        d = d.gcd(E1.ap(p)-E2.ap(p))
        if d<=m_max:
            return False, p, d
        if p>p_max:
            return True, p, d

def test_conductor(N, m_max=17, p_max=1000, verbose=False):
    """
    Return whether any pair of curves of conductor N are mod-p congruent for some p>m_max
    """
    ok  = True
    for i, E1 in enumerate(cremona_optimal_curves([N])):
        for j, E2 in enumerate(cremona_optimal_curves([N])):
            if j<=i:
                continue
            res, p, d = test_cong(E1,E2, m_max, p_max)
            if verbose:
                if res:
                    print("{} & {}: congruent mod {} for primes up to {}".format(E1.label(),E2.label(),d,p))
                else:
                    print("{} & {}: no congruence mod p>{}, using primes up to {}".format(E1.label(),E2.label(),m_max,p))
            ok = ok and not res
    return ok

def test_equal_N(max_N=1000):
    """
    Look for a pair of curves of the same conductor N<=N_max which are mod-p congruent for some p>m_max
    """
    for N in [11..max_N]:
        if N%1000 == 0:
            print(N)
        ok = test_conductor(N, verbose=False)
        if not ok:
            print test_conductor(N, verbose=True)

# Find the sets M_E

def M_E(E, verbose=False):
    """
    Compute the set M_E (defined in the paper)
    """
    t = [(l.prime().gen(), l.discriminant_valuation()) for l in E.local_data() if l.conductor_valuation()==1]
    if verbose:
        print("(q,v_q(D)): {}".format(t))
    ME = sum([[[ti[0],p] for p in ti[1].prime_factors() if p>17] for ti in t], [])
    return ME

# find all nontrivial M_E for curves of conductor up to some bound

def all_M_E(Nmax):
    nc =0
    nc_nontriv = 0
    Ms = {}
    for E in cremona_optimal_curves([11..Nmax]):
        nc += 1
        M = M_E(E)
        if M:
            nc_nontriv += 1
            print E.label(), M
            Ms[E.label()] = M
    print("Out of {} isogeny classes of curves of conductor <= {}, {} have non-trivial M_E".format(nc, Nmax, nc_nontriv))
    qlist = sorted(list(Set(sum([[q for q,p in M] for M in Ms.values()],[]))))
    plist = sorted(list(Set(sum([[p for q,p in M] for M in Ms.values()],[]))))
    print("all p: {}".format(plist))
    print("all q: {}".format(qlist))
    return Ms
