def test_isom(E1,E2, nump=5, verbose=True):
    _,_,_,aa,bb = E1.short_weierstrass_model().ainvs()
    P2Q = ProjectiveSpace(QQ,2)
    F = F_ab(aa,bb)
    DeltaE = -16*(4*aa**3+27*bb**2)
    D = Del(F)
    C = C_covariant(F)
    jdash = E2.j_invariant()
    G = jdash*DeltaE*D**7+4*C**3
    K = K_covariant(F)

    def use_P(P):
        x,y,z = P = list(P)
        d = 2*z*(aa*x**2+3*bb*x*z+2*aa*y*z+3*y**2)
        d2 = d*d
        d3 = d2*d
        assert jdash == -4*C(P)**3/(DeltaE*D(P)**7)
        c4 = C(P)*d2
        c6 = K(P)*d3
        #print("c4={}, c6={}".format(c4,c6))
        E = EllipticCurve([0,0,0,-c4/48,-c6/864])
        if E2.is_isomorphic(E):
            print("Success! Curves are symplectically isomorphic")
            return True, (aa,bb), P
        else:
            print("Wrong curve!  E2 = {} but we get {}".format(E2.ainvs(),E.global_minimal_model().ainvs()))
            res = E2.is_quadratic_twist(E)
            print("Quadratic twist by {}".format(res))
            return False

    Qset = P2Q.subscheme([F,G])
    if nump==0:
        print("Looking for a rational solution directly...")
        point_list = Qset.rational_points()
        if len(point_list)==0:
            print("No rational solution")
            return False
        P = point_list[0]
        print("Found rational point P={}".format(P))
        return use_P(P)

    def points_mod_p(p):
        if verbose: 
            print("p = {}".format(p))
        k=GF(p)
        P2k = ProjectiveSpace(k,2)
        Modpset = P2k.subscheme([F.change_ring(k),G.change_ring(k)])
        return Modpset.rational_points()

    # At each stage we'll have a list of points modulo some product of primes.  Then we'll find the solutions modulo the next prime and CRT together
    point_list = []
    prime_list = []
    N = 1
    p = next_prime(2**25)
    while not p%7 in [3,5]:
        p = next_prime(p)
    while len(prime_list)<nump:
        p = next_prime(p)
        while not p%7 in [3,5]:
            p = next_prime(p)
        pts = points_mod_p(p)
        pts = [[ZZ(c) for c in list(pt)] for pt in pts]
        if verbose:
            print("Found {} points modulo {}: {}".format(len(pts),p,pts))
        if len(pts)==0:
            return False
        success = False
        for P in pts:
            P = P2Q(lift_points([P],[p]))
            if P in Qset:
                if verbose:
                    print("success using p={}: solution is {}".format(p,P))
                success = True
            if P[2]!=1:
                print("Point = {}".format(P))

        if N==1:
            point_list = pts
            prime_list = [p]
            N = p
        else:
            point_list = [CRT_points([P1,P2],[N,p]) for P1,P2 in cartesian_product_iterator([point_list,pts])]
            prime_list.append(p)
            N *= p
        if verbose:
            print("We now have {} points mod {}: {}".format(len(point_list),N, point_list))

        for pt in point_list:
            x=pt[0]
            y=pt[1]
            M = Matrix([[x,y,1],[N,0,0],[0,N,0]])
            P = P2Q(list(M.LLL().row(0)))
            if P in Qset:
                if verbose:
                    print("success! P = {}".format(P))
                success=True
                break
            else:
                if verbose:
                    print("No luck with {}".format(P))

        if success:
            return use_P(P)
        if verbose:
            print("No luck so far, use another prime")

    print("After trying {} primes, no global solutions found".format(nump))
    return False

