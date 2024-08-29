SetLogFile("Limit_values_r.out");
D := 37;

/*
The next function computes the set X_\ell'.
We use a moderate speed-up with respect to the definition:
instead of checking if a given element is or is not an n-th
root of unity, we use the fact that the n-th roots of unity
are the powers of g^p, where g is a generator of F_\ell*
*/
function PopulateXell1(p, n)
	ell := p*n+1;
	pe := PrimitiveElement(GF(ell));
	Xell2 := [ pe^(p*b)+D : b in [1..n] ];
	Xell1 := [];
	for x in Xell2 do
		if IsSquare(x) then
			_, rt := IsSquare(x);
			Append(~Xell1, rt);
			Append(~Xell1, -rt);
		end if;
	end for;
	return Xell1;
end function;

/*
We now loop over all primes up to 1.5*10^5.
BadPrimes will list those primes for which
this procedure cannot prove that r = \pm 1.
*/

BadPrimes := [];
for p in [j : j in [3..150000] | IsPrime(j) ] do

	rPossible := {-Integers()!( (p-1)/2 )..Integers()!( (p-1)/2 )};
	n := 1;
	count := 0;
	while #rPossible gt 2 and count lt 15  do	// we look for at most 15 auxiliary primes \ell
		ell := n*p + 1;
		if IsPrime(ell) then
			if LegendreSymbol(D, ell) eq 1 then
				_, theta := IsSquare(GF(ell)!D);
				eta := 6 + theta;
				if Log( eta ) mod p ne 0 then
						// "Found the prime", ell;
						count := count + 1;
						Xell1 := PopulateXell1(p, n);
	
						Rl := { GF(p)!Log(delta + theta) / GF(p)!Log( eta ) : delta in Xell1 | GF(p)!Log(delta + theta) / GF(p)!Log( eta ) eq GF(p)!-Log(delta - theta) / GF(p)!Log( eta )  } join { GF(p)!Log(2*theta) / GF(p)!Log( 6+theta ) } join { -GF(p)!Log(-2*theta) / GF(p)!Log( 6+theta ) };
						rPossible := {r : r in rPossible | GF(p)!r in Rl };
				end if;
			end if;
		end if;
		n := n+1;
	end while;
	"Checked p = " cat Sprint(p) cat ". Only possibilities remaining: r \in " cat Sprint(rPossible) cat ".";
	if #rPossible gt 2 then
		Append(~BadPrimes, p);
	else
		assert rPossible eq {-1, 1};
	end if;
end for;
"Primes for which we do not know that r = \pm 1", BadPrimes;

exit;
