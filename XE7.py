from sage.all import PolynomialRing, vector, Matrix, EllipticCurve, QQ

def F_ab(aa,bb):
    R3 = PolynomialRing(aa.parent(),3,'x')
    X,Y,Z = R3.gens()
    return (aa*X**4+7*bb*X**3 + 3*(Y**2-aa**2)*X**2 -bb*(6*Y+5*aa)*X +(2*Y**3+3*aa*Y**2+2*aa**2*Y-4*bb**2)).homogenize(Z)

def Hessian_matrix(F):
    vars = F.parent().gens()
    return Matrix([[F.derivative(v1, v2) for v1 in vars] for v2 in vars])

def Hessian(F):
    return Hessian_matrix(F).det()

def Del(F):
    return Hessian(F)/54

# Poonen, Schaeffer, Stoll call this -\(\Psi_6(F)\) (note the minus sign)
def Psi6(F):
    return - Del(F)

def C_covariant(F):
    M = Hessian_matrix(F)
    v = Del(F).gradient()
    M = M.augment(vector(v))
    M = M.stack(vector(v+[0]))

    return M.det()/9

# Poonen, Schaeffer, Stoll call this \(\Psi_{14}(F)\)
Psi14 = C_covariant

def K_covariant(F):
    vars = F.parent().gens()
    M = Matrix([[f.derivative(v) for v in vars] for f in [F,Del(F),C_covariant(F)]])
    return M.det()/14

# Poonen, Schaeffer, Stoll call this \(\Psi_{21}(F)\)
Psi21 = K_covariant

def intersection_points(F,G):
    """Given F, G homogeneous in 3 variables, returns a list of their
    intersection points in P^2.  Note that we can just find the
    rational_points() on the associated subscheme of P^2 but over Q
    that takes much longer.
    """
    R3 = F.parent()
    k = R3.base_ring()
    R2 = PolynomialRing(k,2,'uv')
    u,v = R2.gens()
    R1 = PolynomialRing(k,'w')
    w = R1.gens()[0]
    sols = []

    # We stratify the possible points as follows:
    # (1) [0,1,0], checked directly;
    # (2) [1,y,0], roots of a univariate polynomial;
    # (3) [x,y,1], found using resultants

    # Check the point [0,1,0] with X=Z=0:
    if F([0,1,0])==0 and G([0,1,0])==0:
        sols = [[0,1,0]]

    # Find other points [1,y,0] with Z=0:
    f = F([1,w,0])
    g = G([1,w,0])
    h = f.gcd(g)
    sols += [[1,r,0] for r in h.roots(multiplicities=False)]

    # Find all other points [x,y,1] with Z!=0:
    f = F([u,v,1])
    g = G([u,v,1])
    # the following resultant is w.r.t. the first variable u, so is a
    # polynomial in v; we convert it into a univariate polynomial in
    # w:
    res = (f.resultant(g))([1,w])
    for r in res.roots(multiplicities=False):
        h = f([w,r]).gcd(g([w,r]))
        for s in h.roots(multiplicities=False):
            sols.append([s,r,1])
    return sols

def KH0(T):
    return EllipticCurve([0,7,0,0,28*T])

def KH1(T):
    a4 = 7*T**3+7*T**2-19*T-16
    a6 = -T**5+14*T**4+63*T**3+77*T**2+38*T+20
    return EllipticCurve([0,1,0,a4,a6])

def KH2(T):
    a4 = -(45927*T**3+204120*T**2+162432*T+4181)
    a6 = -(531441*T**5 + 12262509*T**4 + 39287997*T**3 + 43008840*T**2 + 8670080*T - 102675)
    return EllipticCurve([0,1,0,a4,a6])

class XE7(object):
    def __init__(self, a, b):
        self._base = a.parent()
        self._a = a
        self._b = b
        self.Eab = EllipticCurve([0,0,0,a,b])
        self._F = F_ab(a,b)
        self.P2C = {}    # P2C is a dict with keys points on XE(7) and values the curve associated with that point

        # NB in two special cases we cannot yet distinguish between 2
        # or 3 possible curves so we store lists of curves, usually
        # with only one time in the list but occasionally 2 or 3

    @staticmethod
    def from_elliptic_curve(E):
        _,_,_,a,b = E.short_weierstrass_model().ainvs()
        return XE7(a,b)

    @staticmethod
    def from_label(lab):
        return XE7.from_elliptic_curve(EllipticCurve(lab))

    def F(self):
        return self._F

    def Del(self, P=None):
        try:
            D = self._Del
        except AttributeError:
            D = self._Del = Del(self._F)
        if P == None:
            return D
        return D(P)

    def C(self, P=None):
        try:
            C = self._C
        except AttributeError:
            C = self._C = C_covariant(self._F)
        if P == None:
            return C
        return C(P)

    def K(self, P=None):
        try:
            K = self._K
        except AttributeError:
            K = self._K = K_covariant(self._F)
        if P == None:
            return K
        return K(P)

    def DeltaE(self):
        try:
            return self._DeltaE
        except AttributeError:
            self._DeltaE = -16*(4*self._a**3+27*self._b**2)
            return self._DeltaE

    def G(self, jdash):
        return jdash*self.DeltaE()*self.Del()**7+4*self.C()**3

    def j(self,P):
        return -4*self.C(P)**3/(self.DeltaE()*self.Del(P)**7)

    def V(self):
        x,y,z = self._F.parent().gens()
        a = self._a
        b = self._b
        return a*x**2 + 3*b*x*z + 2*a*y*z + 3*y**2

    def curve(self, P=None, verbose=False):
        # Given a point on X_E(7), return the symplectically isomorphic curve.
        if P==None:
            return self.Eab
        tP = tuple(P)
        try:
            return self.P2C[tP]
        except KeyError:
            pass

        if verbose:
            print("mapping P={} to its curve".format(P))
        if P==[0,1,0]:
            E2 = self.Eab
            if self._base==QQ:
                E2 = E2.minimal_model()
            self.P2C[tP] = [E2]
            if verbose:
                print("P={} is the base point, returning {}".format(P,E2.ainvs()))
            return [E2]

        a = self._a
        b = self._b

        if P==[1,0,0]: # only when j=0, i.e. a=0
            E2 = EllipticCurve([0,0,0,0,-28/b])
            if self._base==QQ:
                E2 = E2.minimal_model()
            self.P2C[tP] = [E2]
            if verbose:
                print("P={} is a special j=0 point, returning {}".format(P,E2.ainvs()))
            return [E2]

        jP = self.j(P)
        x,y,z = P = list(P)

        if z==0: # j nonzero,  one of the two special points
            #print("P={}".format(P))
            assert (-3*a).is_square()
            j = self.Eab.j_invariant()
            #print("j = {}".format(j))
            u2 = (j-1728)/j
            assert u2.is_square()
            u = u2.sqrt()
            if u==-1: u=-u
            #print("u = {}".format(u))
            T = -49*(1+u)/54
            #print("T = {}".format(T))
            ET = KH0(T)
            assert ET.j_invariant()==j
            d = ET.is_quadratic_twist(self.Eab)
            if not d:
                print("Failure in computation of z=0 curves when j=0")
                return []
            #print("d = {}".format(d))

            # try special curves using Kraus-Halberstadt' parametrizations:
            E2list = []
            for KH in [KH1, KH2]:
                E2 = KH(T).quadratic_twist(d)
                if E2.j_invariant()==jP:
                    if self._base==QQ:
                        E2 = E2.minimal_model()
                    E2list.append(E2)
            if verbose:
                print("P={} is a special z=0 point, returning {}".format(P,[EE2.ainvs() for EE2 in E2list]))
            self.P2C[tP] = E2list
            return E2list

        VP = self.V()(P)
        if VP==0: # a 2-isogeny point
            E2list = [phi.codomain() for phi in self.Eab.isogenies_prime_degree(2)]
            E2list = [EE2 for EE2 in E2list if EE2.j_invariant()==jP]
            if self._base==QQ:
                E2list = [EE2.minimal_model() for EE2 in E2list]
            self.P2C[tP] = E2list
            if verbose:
                print("P={} is a special V=0 point, returning {}".format(P,[EE2.ainvs() for EE2 in E2list]))
            return E2list

        # Generic case
        d = 2*z*VP
        assert d!=0
        c4 = self.C(P)*d**2
        c6 = self.K(P)*d**3
        E2 = EllipticCurve([0,0,0,-c4/48,-c6/864])
        if self._base==QQ:
            E2 = E2.minimal_model()
        self.P2C[tP] = [E2]
        if verbose:
            print("P={} is a general point, returning {}".format(P,E2.ainvs()))
        return [E2]

    def lift_curve(self, Edash, verbose=False):
        for P in self.lift_j(Edash.j_invariant()):
            if verbose:
                print("Testing P={}".format(P))
            for E2 in self.curve(P, verbose=verbose):
                if verbose:
                    print("Testing E2={}".format(E2.ainvs()))
                if E2.is_isomorphic(Edash):
                    if verbose:
                        print("success with E2")
                    return P
                else:
                    if verbose:
                        print("E2 fails")
        return None

    def lift_j(self, jdash):
        return intersection_points(self._F,self.G(jdash))

def test_isom(E1,E2, verbose=False):
    X = XE7.from_elliptic_curve(E1)
    P2 = X.lift_curve(E2, verbose=verbose)
    if P2==None:
        if verbose:
            print("No lifts of  E2 to X_E(7)")
        return False
    if verbose:
        print("Success! curves E1={} and E2={} and are symplectically isomorphic: P={} on X_E1(7) maps to E2".format(E1.ainvs(),E2.ainvs(),P2))
    return True

def test_isom_labels(lab1,lab2, verbose=False):
    E1 = EllipticCurve(lab1)
    E2 = EllipticCurve(lab2)
    if verbose:
        print("Testing {} ={} and {} = {}".format(lab1,E1.ainvs(),lab2,E2.ainvs()))
    return test_isom(E1, E2, verbose=verbose)
