from sage.all import GCD, Infinity, PolynomialRing

def ZeroAtOrigin(pol):
    """
    Return True iff pol(0,0)=0
    """
    return pol(0,0)==0

def PrePol(pol):
    """
    input:
    pol - a polynomial in two variables with no constant term
    output:
    px,py, where px does not depend on y and pol=x*px+y*py
    """
    assert ZeroAtOrigin(pol), "{} is not 0 at origin".format(pol)
    x, y = pol.parent().gens()
    px = pol([x,0])
    py = (pol-px) // y
    assert y*py+px == pol, "bad result of PrePol"
    return px // x, py;

def UnaSe(eta,phi,pol):
    """
    one elementary simplification of
    the polynomial pol modulo the curve
    with equation y*eta+x*phi=0.
    """
    assert not ZeroAtOrigin(eta), "{} is 0 at origin".format(eta)
    pox, poy = PrePol(pol)
    return pox*eta-poy*phi

def Eval0(cur,fra):
    """
    perform the evaluation at the origin
    on the curve cur=0 of the rational
    function fra, where fra is the ordered
    list fra=[numerator,denominator]
    """
    x, y = cur.parent().gens()
    phi,eta = PrePol(cur)
    gcd = GCD([cur] + fra)
    if ZeroAtOrigin(gcd):
        raise ValueError,  "the numerator and denominator vanish identically"
    fr0 = [ff // gcd for ff in fra]
    while True:
        preva = [nn(0,0) for nn in fr0]
        if preva != [0,0]:
            return preva
        fr0 = [UnaSe(eta,phi,ff) for ff in fr0]
        gcd = GCD(fr0)
        fr0= [ff // gcd for ff in fr0]

def Eval(cur,fra,pto):
    """
    same as Eval0, but also takes as input the coordinates
    pto of a point where the function should be evaluated.
    """
    xx, yy = cur.parent().gens()
    x0, y0 = pto
    nuli = [pp([xx+x0,yy+y0]) for pp in [cur] + fra]
    return Eval0(nuli[0],nuli[1:])

def EvalHomog(Cur, Fun, Pt):
    """
    Evaluate Fun=[Num,Den] = Num/Den at Pt on Cur=0.

    Fun, Num Den are homogeneous in 3 variables with
    deg(Num)=deg(Den), and Cur(Pt)==0.
    """
    Num, Den = Fun
    assert all(pol.is_homogeneous() for pol in [Cur, Num, Den]), "Input polynomials not homogeneous in EvalHomog"
    assert Num.degree()==Den.degree(), "Numerator and Denominator have different degrees in EvalHomog"

    # Check that Pt is a smooth point on Cur=0:
    assert Cur(Pt)==0, "Point {} not on curve {} in EvalHomog".format(Pt,Cur)
    assert not all (dF(Pt)==0 for dF in [Cur.derivative(v) for v in Cur.parent().gens()]), "Point {} is not a smooth point on curve {} in EvalHomog".format(Pt,Cur)

    # deal with easy case, not 0/0
    num = Num(Pt)
    den = Den(Pt)
    if [num,den] == [0,0]: # else easy

        # find a suitable dehomogenization
        x0,y0,z0 = Pt
        x, y = PolynomialRing(Cur.base_ring(),2,['x','y']).gens()
        if z0:
            xy = [x,y,1]
            p = [x0/z0,y0/z0]
        elif y0:
            xy = [x,1,y]
            p = [x0/y0,0]
        else:
            xy = [1,x,y]
            p = [0,0]
        num, den = Eval(Cur(xy), [Num(xy),Den(xy)], p)
    return Infinity if den==0 else num/den


def test():
    from sage.all import QQ
    R2 = PolynomialRing(QQ,2)
    x, y = R2.gens()
    ef = y+x^2
    fun = x^3+x*y

    try:
        print(Eval0(ef,[ef,fun]))
        print("not OK")
    except ValueError:
        print("OK")

    print(Eval0(ef,[fun+x^2,fun]))

    F = x^2+y^2-1
    print(Eval(F, [x,1-y], [0,1]))
    print(Eval(F, [1+y,x], [0,1]))
    print(Eval(F, [1+y,x], [-1,0]))
    print(Eval(F, [x,1-y], [-1,0]))

    R3 = PolynomialRing(QQ,3)
    X, Y, Z = R3.gens()
    F = X^2+Y^2-Z^2
    print(EvalHomog(F, [X,Z-Y], [0,1,1]))
    print(EvalHomog(F, [Z+Y,X], [0,1,1]))
    print(EvalHomog(F, [Z+Y,X], [-1,0,1]))
    print(EvalHomog(F, [X,Z-Y], [-1,0,1]))
    print(EvalHomog(F, [X,Z-Y], [3,4,5]))
