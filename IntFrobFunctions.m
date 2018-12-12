function DiscList(x)
  if ((x mod 4) in [2,3]) or (x ge 0) then
    return [];
  end if;
  D, h := Squarefree(x);
  if (D mod 4) in [2,3] then
    D := D * 4;
    h := h div 2;
  end if;
  L := [];
  for d in Divisors(h) do
    Append(~L, D*d^2);
  end for;
  return L;
end function;



function EndomorphismRingDiscriminant(E) 
  a := TraceOfFrobenius(E);				
  k := BaseField(E);					
  q := #k;												
  p := Characteristic(k);										
  r := Valuation(q, p);
  Delta := a^2 - 4*q;											
  if Delta eq 0 then
    return 0, -1, a, false;
  end if;
  if (a mod p) eq 0 then
    if ((p mod 4) eq 3) and (a eq 0) and ((r mod 2) eq 1) then
      if #Generators(SylowSubgroup(TorsionSubgroup(E), 2)) eq 2 then
        return (-1)*p, 2*p^((r-1) div 2), a, false;
      else
        return (-4)*p, p^((r-1) div 2), a, false;
      end if;
    else
      D, h := Squarefree(Delta);
      if (D mod 4) in [2,3] then
        D := D * 4;
        h := h div 2;
      end if;
      return D, h, a, false;
    end if;
  else
    j_E := jInvariant(E);
    Discs := DiscList(Delta);
    for D in Discs do
      if Evaluate(ChangeRing(HilbertClassPolynomial(D), k), j_E) eq 0 then
        return D, Floor(SquareRoot(Delta div D)), a, true;
      end if;
    end for;
  end if;
end function; 



function IntegralFrobenius(E)
  D, b, a, flag := EndomorphismRingDiscriminant(E);
  if D eq 0 then
    return Matrix([[a div 2, 0], [0, a div 2]]);
  end if;
  Delta := D*b^2;
  return Matrix([[(a - b*D) div 2, (b*D*(1-D)) div 4], [b, (a + b*D) div 2]]);
end function;




