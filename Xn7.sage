# First we define H as a subgroup of index 7 in SL(2,7).  It is more
#  convenient to use SL rather than PSL, so this H has order 16 not 8.

G=SL(2,7)
g=G([9,16,5,9])
assert g.order()==8
h=G([23,53,-10,-23])
assert h.order()==4
H=G.subgroup([g,h])
assert G.order()==21*H.order()

# Now we compute coset representatives for H in G
eqH = lambda g1,g2: g1*g2^(-1) in H
coset_reps = [G(1)]
for g in G:
    if not any([eqH(g,h) for h in coset_reps]):
        coset_reps += [g]
assert len(coset_reps)==21

# and a function for identifying the coset rep for any group element
which_coset = lambda g: [h for h in coset_reps if eqH(g,h)][0]

# Every element of G permutes the cosets by right multiplication.  We compute this for the matrices T, S and TS
S=G([0,-1,1,0])
T=G([1,1,0,1])
TS=T*S
S_map = lambda g: which_coset(g*S)
T_map = lambda g: which_coset(g*T)
TS_map = lambda g: which_coset(g*TS)

# To see these as actual permutations:
pS=Permutation([1+coset_reps.index(S_map(coset_reps[i])) for i in range(21)])
pTS=Permutation([1+coset_reps.index(TS_map(coset_reps[i])) for i in range(21)])
pT=Permutation([1+coset_reps.index(T_map(coset_reps[i])) for i in range(21)])
assert pT*pS==pTS
assert pT.cycle_type() == [7]*3
assert pTS.cycle_type() == [3]*7
assert pS.cycle_type() == [2]*8 + [1]*5
print("S: {}".format(pS.cycle_tuples()))
print("T: {}".format(pT.cycle_tuples()))
print("TS: {}".format(pTS.cycle_tuples()))

# These permutations are all we need to define a subgroup of SL(2,Z):
G = ArithmeticSubgroup_Permutation(S2=pS,S3=pTS)
assert G.genus()==0
assert G.index()==21
assert G.cusp_widths()==[7,7,7]

# which has two (conjugate) "surgroups":
G1 = G.surgroups().next()
assert G1.index()==7
assert G1.ncusps()==1
assert G1.cusp_widths()==[7]
assert G1.nu2()==3
assert G1.nu3()==1

# hence if s is a Hauptmodul for G1 then j is a rational function of s
# of degree 7 of the form linear*quadratic^3/(linear)^7, w.l.o.g. a
# polynomial f(s)=s*(s^2+a*s+b)^3 such that
# f(s)-1728=(cubic)*(quadratic^2)
#
# We set up equations to solve for the unknown coefficients
A.<a1,a2,b1,b2,b3,c1,c2>=QQ[]
B.<s>=A[]
Pa=B([a2,a1,1])
Pb=B([b3,b2,b1,1])
Pc=B([c2,c1,1])
pol=s*Pa^3-1728-Pb*Pc^2
rels=pol.coefficients()
I=Ideal(rels)
assert I.dimension()==0
# The last line means that the number of solutions is finite.

# There are no rational points:
I.variety()

# but we expect there to be points over a quadratic field (since there were 2 surgroups) and for that field to be Q(sqrt(-7)), as that is the quadratic subfield of Q(zeta_7).
K.<a>=NumberField(x^2+x+2)
sols = I.variety(K); sols

# There are 2 solutions, whic must be Galois conjugates.
sola = dict([(v,sols[0][v]) for v in A.gens()]); sola
solb = dict([(v,sols[1][v]) for v in A.gens()]); solb
# and check that these values do satisfy all the equations:
assert [r.subs(sola) for r in rels] == [0, 0, 0, 0, 0, 0, 0]
assert [r.subs(solb) for r in rels] == [0, 0, 0, 0, 0, 0, 0]

# So now we can set up the rational function f(s) (actually a polynomial) and check that it has the correct properties:
S.<s> = K[]
f = s*(s^2+sola[a1]*s+sola[a2])^3
fbar = s*(s^2+solb[a1]*s+solb[a2])^3
g = f-1728
gbar = fbar-1728
assert g == (s^3+sola[b1]*s^2+sola[b2]*s+sola[b3]) * (s^2+sola[c1]*s+sola[c2])^2
assert gbar == (s^3+solb[b1]*s^2+solb[b2]*s+solb[b3]) * (s^2+solb[c1]*s+solb[c2])^2
"The degree 7 polynomial"
f.factor()
[(p.degree(),e) for p,e in f.factor()]
g.factor()
[(p.degree(),e) for p,e in (f-1728).factor()]


# The map from the t-line to the s-line is given by a rational function in t of degree 3. It is split over s=infinity so the denominator p(t) has 3 distinct roots; we use Elkies's polynomial.  Secondly we have ramification of order 3 above s=0 so the numerator is (t-b1)^3 for some b1.  Finally, two of the simple roots of g must split as 2+1, and we take these to be the conjugate roots.
h = g.factor()[1][0]; h
hbar = gbar.factor()[1][0]; hbar
A.<a1,a2,a3,a4,b1,b2,b3,b4,c,l>=QQ[]
At.<t> = A[]
p = t^3-7*t^2+7*t+7
# Another possible choice of p -- simpler?
#p = t^3+t^2-2*t+1

hnorm = h*hbar
H = hnorm(l*(t-c)^3/p).numerator()
#H = h(l*(t-c)^3/p).numerator(); H

Pa = At([a4,a3,a2,a1,1])
Pb = At([b4,b3,b2,b1,1])

Hdiff = H - H.leading_coefficient()*Pa*Pb^2
Hdiff.degree()
I = Ideal(Hdiff.coefficients()); I
print("computing I.dimension()")
I.dimension()
print("computing I.variety()")
I.variety()








