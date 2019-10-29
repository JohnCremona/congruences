from sage.all import EllipticCurve, load, save

from testcong import make_hash, test_cong, test_irred, report
import sys

try:
    hashtab11_50 = load('hashtab11_50')
except IOError:
    hashtab11_50 = make_hash(11,11,500000,50)
    hashtab11_50 = dict([(k,v) for k,v in hashtab11_50.items() if len(v)>1])
    save(hashtab11_50, 'hashtab11_50')
    len(hashtab11_50)

def find_bad_pairs(ht=hashtab11_50):
    bad_pairs = []
    for s in ht.values():
        if len(s)>1:
            E1 = EllipticCurve(s[0])
            for r in s[1:]:
                E2 = EllipticCurve(r)
                res, info = test_cong(11,E1,E2, mumax=10^7)
                if not res:
                    report(res,info,11,s[0],r)
                    bad_pairs.append([s[0],r])
    return bad_pairs

# bad_pairs = find_bad_pairs(hashtab7_50)
# previous cell takes ages; this is the output

bad_pairs = []
isom_sets = [s for s in hashtab11_50.values() if len(s)>1]
len(isom_sets)
isom_sets_red = []
isom_sets_irred = []
for s in isom_sets:
    isom_sets_irred.append(s) if test_irred(s) else isom_sets_red.append(s)
print("{} irreducible sets, {} reducible sets".format(len(isom_sets_irred),len(isom_sets_red)))

from collections import Counter
red_sizes = Counter()
irred_sizes = Counter()

for s in isom_sets_irred:
        irred_sizes[len(s)] += 1
print("irred sizes: {}".format(irred_sizes))

assert len(isom_sets_red)==0
for s in isom_sets_red:
        red_sizes[len(s)] += 1
print("red sizes: {}".format(red_sizes))

assert [len(s)==2 for s in isom_sets_irred)
irred_pairs = isom_sets_irred
print("{}mod 11 irreducible pairs".format(len(irred_pairs)))


# Output pairs for Magma

np = 0
fp = "mod11_pairs.m"
out = open(fp, "w")
out.write('pairs := [\\\n')
for s in irred_pairs[:-1]:
        #print(s[0],s[1])
        out.write('["{}", "{}"],\\\n'.format(s[0],s[1]))
        np += 1
s = irred_pairs[-1]
out.write('["{}", "{}"]\\\n'.format(s[0],s[1]))
np += 1
out.write('];\n')
out.close()
print("Wrote {} pairs to {}".format(np, fp))
