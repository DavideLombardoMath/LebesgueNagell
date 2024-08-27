SetLogFile("r_1_for_D_equal_3.out");
D := 3;

/*
The two newforms are rational and correspond to the following elliptic curves
*/
E1 := EllipticCurve([0, -1, 0, -32, -60]);
E2 := EllipticCurve([0, +1, 0, -32, +60]);
Es := [E1, E2];


/*
The next function returns the coefficient a_\ell of the i-th newform
*/
function a_ell(ell, i)
	return TraceOfFrobenius(ChangeRing(Es[i], GF(ell)));
end function;


/*
The next block of code tests that our fast method to compute the
coefficients of the F_i via point counting on elliptic curves
returns the correct result for all primes up to 10^4.
The creation of the space of newforms require CHIMP (https://github.com/edgarcosta/CHIMP)

chi := DirichletCharacter("96.1");
S:= CuspForms(chi, 2);
N := Newforms(S);
F1 := N[2][1];
F2 := N[1][1];


for ell in [i : i in [7..10^4] | IsPrime(i) ] do
	assert Coefficient(F1, ell) eq a_ell(ell, 1);
end for;
for ell in [i : i in [7..10^4] | IsPrime(i) ] do
	assert Coefficient(F2, ell) eq a_ell(ell, 2);
end for;
*/



/*
The next function computes the Frobenius trace a_\ell(E_\delta)
*/
function a_ell_positivecharacteristic(ell, delta)
	GFell := GF(ell);
	E := EllipticCurve([GF(ell)!0,2*delta,0,D,0]);
	return TraceOfFrobenius(E);
end function;

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
We now loop over the three newforms and over all primes
up to 10^5. This is much larger than what is needed, but
the computation is fast anyway.
*/
for indexForm in [1..2] do
	"=== Checking form number", indexForm, "===";
	for p in [j : j in [11..10^5] | IsPrime(j) ] do

		rPossible := {-Integers()!( (p-1)/2 )..Integers()!( (p-1)/2 )};
		n := 1;
		while not (rPossible subset {-1, 1}) do	// it suffices to rule out all values of r except these two
			ell := n*p + 1;
			if IsPrime(ell) then
				if LegendreSymbol(D, ell) eq 1 then
					_, theta := IsSquare(GF(ell)!D);
					if (2+theta)^n ne 1 then
						if GF(p)!a_ell(ell, indexForm)^2 ne (ell+1)^2 then
							Xell1 := PopulateXell1(p, n);
	
							/*
							The next two lines can be used to test that the result of PopulateXell1 agree
							with the calculation based on the definition. They are commented because (for
							large primes) they are computationally expensive.
							*/
							/*
							time Xell1bis := [ delta : delta in GF(ell) | (delta^2-D)^n eq 1 ];
							assert {x : x in Xell1bis} eq { x : x in Xell1 };
							*/

							assert (2 in Xell1);
							Target_a_ell := a_ell(ell, indexForm);
							Xell := [ delta : delta in Xell1 | a_ell_positivecharacteristic(ell, delta) mod p eq Target_a_ell mod p ];
							Rl := { GF(p)!Log(delta + theta) / GF(p)!Log( 2+theta ) : delta in Xell };
							rPossible := {r : r in rPossible | GF(p)!r in Rl};
						end if;
					end if;
				end if;
			end if;
			n := n+1;
		end while;
	"Checked p = " cat Sprint(p) cat ". Only possibilities remaining: r \in " cat Sprint(rPossible) cat ".";
	end for;
end for;

/*
The very fact that the script terminates implies that for every p < 10^5 we have found
a combination of auxiliary primes \ell that forces r \in {-1, +1}
*/

exit;
