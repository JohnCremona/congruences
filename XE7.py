from sage.all import PolynomialRing, vector, Matrix, EllipticCurve, QQ#, Infinity
#from eval import EvalHomog

def F_ab(aa,bb):
    """
    Ternary quartic defining the curve X_E(7) for E: Y^2=X^3+a*X+b
    """
    X,Y,Z = PolynomialRing(aa.parent(),3,'x').gens()
    return (aa*X**4+7*bb*X**3 + 3*(Y**2-aa**2)*X**2 -bb*(6*Y+5*aa)*X +(2*Y**3+3*aa*Y**2+2*aa**2*Y-4*bb**2)).homogenize(Z)

def G_ab(aa,bb):
    """
    Ternary quartic defining the curve X_E^-(7) for E: Y^2=X^3+a*X+b
    """
    X,Y,Z = PolynomialRing(aa.parent(),3,'x').gens()
    # cut-and-pasted from Tom Fisher's https://www.dpmms.cam.ac.uk/~taf1000/papers/congr-check.m
    G = (-aa**2*X**4 + 2*aa*bb*X**3*Y - 12*bb*X**3*Z - (6*aa**3 + 36*bb**2)*X**2*Y**2
            + 6*aa*X**2*Z**2 + 2*aa**2*bb*X*Y**3 - 12*aa*bb*X*Y**2*Z + 18*bb*X*Y*Z**2
            + (3*aa**4 + 19*aa*bb**2)*Y**4 - (8*aa**3 + 42*bb**2)*Y**3*Z + 6*aa**2*Y**2*Z**2
            - 8*aa*Y*Z**3 + 3*Z**4)
    return G

def Hessian_matrix(F):
    vars = F.parent().gens()
    return Matrix([[F.derivative(v1, v2) for v1 in vars] for v2 in vars])

def Hessian(F):
    return Hessian_matrix(F).det()

def Del(F):
    return Hessian(F)/54

# Poonen, Schaeffer, Stoll call this -\(\Psi_6(F)\) (note the minus sign)
# This is Fisher's H:
def Psi6(F):
    return - Del(F)

H = Psi6

# This is Fisher's c_4:
def C_covariant(F):
    M = Hessian_matrix(F)
    v = Del(F).gradient()
    M = M.augment(vector(v))
    M = M.stack(vector(v+[0]))

    return M.det()/9

# Poonen, Schaeffer, Stoll call this \(\Psi_{14}(F)\)
Psi14 = c4 = C_covariant

# This is *minus* Fisher's c_6 (his c_6 would have Psi6 instead of Del):
def K_covariant(F):
    vars = F.parent().gens()
    M = Matrix([[f.derivative(v) for v in vars] for f in [F,Del(F),C_covariant(F)]])
    return M.det()/14

# Poonen, Schaeffer, Stoll call this \(\Psi_{21}(F)\)
Psi21 = K_covariant

def c6(F):
    return - K_covariant(F)

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

# The following three families are the ones in the first
# Kraus-Halberstad paper and were originally used to cater for some of
# the special points on X_E(7), before we implemented Fisher's
# formulas.  No longer needed.

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

# Class for the curves X_E(7) and X_E^-(7).  Constructed either from a
# curve E using XE7.from_elliptic_curve(E) or from a label using
# XE7.from_label(lab).  By default constructs the symplectic version
# X_E(7); use symplectic=False for X_E^-(7).

class XE7(object):
    def __init__(self, a, b, symplectic=True):
        self._base = a.parent()
        self._symplectic = symplectic
        self._a = a
        self._b = b
        self.Eab = EllipticCurve([0,0,0,a,b])
        self._DeltaE = -16*(4*a**3+27*b**2)
        if symplectic:
            self._F = F_ab(a,b)
        else:
            self._F = G_ab(a,b)
        self._Del = Del(self._F)
        self._K = K_covariant(self._F)
        self._C = C_covariant(self._F)
        if symplectic:
            assert self.j([0,1,0])==self.Eab.j_invariant()
        # else there is no base-point since E is normally not
        # antisymplectically isomorphic to itself!
        self.P2C = {}    # P2C is a dict with keys points on XE(7) and values the curve associated with that point

        # NB in two special cases we cannot yet distinguish between 2
        # or 3 possible curves so we store lists of curves, usually
        # with only one time in the list but occasionally 2 or 3

    @staticmethod
    def from_elliptic_curve(E, symplectic=True):
        _,_,_,a,b = E.short_weierstrass_model().ainvs()
        return XE7(a,b,symplectic=symplectic)

    @staticmethod
    def from_label(lab, symplectic=True):
        return XE7.from_elliptic_curve(EllipticCurve(lab),symplectic=symplectic)

    def F(self):
        return self._F

    def Del(self, P=None):
        D = self._Del
        return D(P) if P else D

    def C(self, P=None):
        C = self._C
        return C(P) if P else C

    def K(self, P=None):
        K = self._K
        return K(P) if P else K

    def DeltaE(self):
        return self._DeltaE

    def Psi(self):
        D = self._DeltaE / 4
        return D if self._symplectic else D**2

    def j(self,P):
        return -self.C(P)**3/(self.Psi()*self.Del(P)**7)

    def j_poly(self, jdash):
        return jdash*self.Psi()*self.Del()**7+self.C()**3

    def V(self):
        x,y,z = self._F.parent().gens()
        a = self._a
        b = self._b
        return a*x**2 + 3*b*x*z + 2*a*y*z + 3*y**2

    # See Fisher p.27 for the d_1j; cut-and-pasted from Tom Fisher's
    # https://www.dpmms.cam.ac.uk/~taf1000/papers/congr-check.m
    # for d22, d33, d44
    def d11(self, P=None):
        x,y,z = P if P else self._F.parent().gens()
        a = self._a
        b = self._b
        if self._symplectic:
            return -2*a*x**2*z - 6*b*x*z**2 - 6*y**2*z - 4*a*y*z**2
        else:
            return -7*a*x**2*y + 6*x**2*z + 3*a**2*y**3 - 8*a*y**2*z + 3*y*z**2

    def d12(self, P=None):
        x,y,z = P if P else self._F.parent().gens()
        a = self._a
        b = self._b
        if self._symplectic:
            return 2 * x * self.V()
        else:
            return 2*a*x**3 + 12*b*x**2*y - 2*a*x*y*z - 3*a*b*y**3 + 6*b*y**2*z

    def d13(self, P=None):
        x,y,z = P if P else self._F.parent().gens()
        a = self._a
        b = self._b
        if self._symplectic:
            return 4 * z * (3*b*x**2 - 2*a*x*y - 2*a**2*x*z - 3*b*y*z - 2*a*b*z**2)
        else:
            return 2*a**2*x*y**2 - 10*a*x*y*z + 6*x*z**2 + 5*a*b*y**3 - 12*b*y**2*z

    def d14(self, P=None):
        x,y,z = P if P else self._F.parent().gens()
        a = self._a
        b = self._b
        if self._symplectic:
            return 4 * z * (a**2*x**2 + 3*b*x*y + 4*a*b*x*z + a*y**2 + 3*b**2*z**2)
        else:
            return 2*a**2*x**2*y - 3*a*x**2*z + 5*a*b*x*y**2 - 12*b*x*y*z - 3*a**2*y**2*z + 8*a*y*z**2 - 3*z**3

    def d22(self, P=None):
        x,y,z = P if P else self._F.parent().gens()
        a = self._a
        b = self._b
        if self._symplectic:
            return 8*b*x**3 - 4*a*x**2*y - 6*a**2*x**2*z - 12*b*x*y*z - 10*a*b*x*z**2 + 4*y**3 +   6*a*y**2*z + 4*a**2*y*z**2 - 8*b**2*z**3
        else:
            return -8*b*x**3 + 3*a**2*x**2*y + 4*a*x**2*z - 2*a*b*x*y**2 + 12*b*x*y*z   + (-3*a**3 - 16*b**2)*y**3 + 2*a**2*y**2*z - 3*a*y*z**2 + 2*z**3

    def d33(self, P=None):
        x,y,z = P if P else self._F.parent().gens()
        a = self._a
        b = self._b
        if self._symplectic:
            return 18*b*x**3 - 12*a*x**2*y - 8*a**2*x**2*z + 12*b*x*y*z + 10*a*b*x*z**2 -   8*a*y**2*z - 12*a**2*y*z**2 + (-8*a**3 - 24*b**2)*z**3
        else:
            return -a**2*x**2*y + 2*a*b*x*y**2 - 12*b*x*y*z + (-7*a**3 - 36*b**2)*y**3 + 6*a**2*y**2*z - 7*a*y*z**2 + 6*z**3

    def d44(self, P=None):
        x,y,z = P if P else self._F.parent().gens()
        a = self._a
        b = self._b
        if self._symplectic:
            return -6*a*b*x**3 + 4*a**2*x**2*y + (-8*a**3 - 42*b**2)*x**2*z - 20*a*b*x*y*z -   22*a**2*b*x*z**2 + (4*a**3 - 12*b**2)*y*z**2 - 26*a*b**2*z**3
        else:
            return -a**3*x**2*y + 2*a**2*x**2*z - 2*a**2*b*x*y**2 + 2*a*b*x*y*z + 6*b*x*z**2 + (-3*a**4 - 19*a*b**2)*y**3 + (8*a**3 + 42*b**2)*y**2*z - 3*a**2*y*z**2

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
        if self._symplectic and P==[0,1,0]:
            E2 = self.Eab
            if self._base==QQ:
                E2 = E2.minimal_model()
            self.P2C[tP] = [E2]
            if verbose:
                print("P={} is the base point, returning {}".format(P,E2.ainvs()))
            return [E2]

        ds = (d for d in (self.d11(P), self.d22(P), self.d33(P), self.d44(P)))

        d = 0
        while d==0:
            d = ds.next()
            if verbose: print("d={}".format(d))

        if not self._symplectic:
            d *= self.DeltaE()
        c4 = self.C(P) * d**2
        c6 = -self.K(P) * d**3

        E2 = EllipticCurve([0,0,0,-c4/48,-c6/864])
        assert E2.j_invariant()==self.j(P)
        if self._base==QQ:
            E2 = E2.minimal_model()
        self.P2C[tP] = [E2]
        if verbose:
            print("P={} is a general point, returning {}".format(P,E2.ainvs()))
        return [E2]

        # jP = self.j(P)
        # x,y,z = P = list(P)

        # if z==0: # j nonzero,  one of the two special points
        #     #print("P={}".format(P))
        #     assert (-3*a).is_square()
        #     j = self.Eab.j_invariant()
        #     #print("j = {}".format(j))
        #     u2 = (j-1728)/j
        #     assert u2.is_square()
        #     u = u2.sqrt()
        #     if u==-1: u=-u
        #     #print("u = {}".format(u))
        #     T = -49*(1+u)/54
        #     #print("T = {}".format(T))
        #     ET = KH0(T)
        #     assert ET.j_invariant()==j
        #     d = ET.is_quadratic_twist(self.Eab)
        #     if not d:
        #         print("Failure in computation of z=0 curves when j=0")
        #         return []
        #     #print("d = {}".format(d))

        #     # try special curves using Kraus-Halberstadt' parametrizations:
        #     E2list = []
        #     for KH in [KH1, KH2]:
        #         try:
        #             E2 = KH(T).quadratic_twist(d)
        #             if E2.j_invariant()==jP:
        #                 if self._base==QQ:
        #                     E2 = E2.minimal_model()
        #                 E2list.append(E2)
        #         except ArithmeticError:
        #             # e.g. E1='28224fo1', lifting '65088dg2' to P=[1:14:0] gives T=-3 and KH1(-3) is singular 
        #             continue
                
        #     if verbose:
        #         print("P={} is a special z=0 point, returning {}".format(P,[EE2.ainvs() for EE2 in E2list]))
        #     self.P2C[tP] = E2list
        #     return E2list

        # VP = self.V()(P)
        # if VP==0: # a 2-isogeny point
        #     E2list = [phi.codomain() for phi in self.Eab.isogenies_prime_degree(2)]
        #     E2list = [EE2 for EE2 in E2list if EE2.j_invariant()==jP]
        #     if self._base==QQ:
        #         E2list = [EE2.minimal_model() for EE2 in E2list]
        #     self.P2C[tP] = E2list
        #     if verbose:
        #         print("P={} is a special V=0 point, returning {}".format(P,[EE2.ainvs() for EE2 in E2list]))
        #     return E2list

        # # Generic case
        # d = 2*z*VP
        # assert d!=0
        # c4 = self.C(P)*d**2
        # c6 = self.K(P)*d**3
        # E2 = EllipticCurve([0,0,0,-c4/48,-c6/864])
        # if self._base==QQ:
        #     E2 = E2.minimal_model()
        # self.P2C[tP] = [E2]
        # if verbose:
        #     print("P={} is a general point, returning {}".format(P,E2.ainvs()))
        # return [E2]

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
                        print("E2 candidate fails")
                        print(" (twist factor = {})".format(E2.is_quadratic_twist(Edash)))
        return None

    def lift_j(self, jdash):
        return intersection_points(self._F,self.j_poly(jdash))

def test_isom(E1,E2, symplectic=True, verbose=False):
    X = XE7.from_elliptic_curve(E1, symplectic=symplectic)
    P2 = X.lift_curve(E2, verbose=verbose)
    if P2==None:
        if verbose:
            print("No lifts of  E2 to X_E{}(7)".format("" if symplectic else "^-"))
        return False
    if verbose:
        print("Success! curves E1={} and E2={} and are {}symplectically isomorphic: P={} on X_E1(7) maps to E2".format("" if symplectic else "anti-",E1.ainvs(),E2.ainvs(),P2))
    return True

def test_isom_labels(lab1,lab2, symplectic=True, verbose=False):
    E1 = EllipticCurve(lab1)
    E2 = EllipticCurve(lab2)
    if verbose:
        print("Testing {} ={} and {} = {}".format(lab1,E1.ainvs(),lab2,E2.ainvs()))
    return test_isom(E1, E2, symplectic=symplectic, verbose=verbose)
