SetLogFile("r_3_for_D_equal_5.out");
D := 5;

/*
The two rational newforms correspond to the following elliptic curves
*/
E1 := EllipticCurve([0, 1, 0, -6, 4]);
E2 := EllipticCurve([0, -1, 0, -6, -4]);
Es := [E1, E2];


/*
Computing the coefficients of the irrational newform is too slow. We then use
the fact that the L-function of the newform is the L-function of the genus 2
curve https://www.lmfdb.org/Genus2Curve/Q/25600/f/512000/1. Over Q(i), the
Jacobian of this curve splits (up to isogeny) as the square of the elliptic 
curve https://www.lmfdb.org/EllipticCurve/2.0.4.1/1600.2/b/3. Thus, at least
for \ell \equiv 1 \pmod 4, the coefficients of our irrational newform can be
read off the point-counting of the elliptic curve in question.
*/


R<x> := PolynomialRing(Rationals()); K<a> := NumberField(R![1, 0, 1]);
Zi := MaximalOrder(K);
Ei := EllipticCurve([K![0,0],K![-1,1],K![0,0],K![3,6],K![5,-1]]);

function FastCoefficientIrrationalNewform(ell)
	if not ell mod 4 eq 1 then
		error "Not implemented";
	end if;

	/*
	We construct the relevant elliptic curve directly over a finite field
	*/
	F := GF(ell);
	_, i := IsSquare(F!(-1));
	Eell1 := EllipticCurve([F!0,-1+i,0,3+6*i,5-i]);
	lp1 := LPolynomial(Eell1);

	/*
	and we compute the corresponding trace of Frobenius
	*/
	t1 := -Coefficient(lp1, 1);

	/*
	Since E is a Q-curve, it's isogenous to its conjugate
	Hence it does not matter which square root of -1 we use
	to define the reduction modulo \ell and compute the L-polynomial.
	We test this fact by computing the Frobenius trace of the curve
	obtained by replacing i with -i in the defining equation and
	checking that it agrees with the previously computed Frobenius
	trace
	*/
	Eell2 := EllipticCurve([F!0,-1-i,0,3-6*i,5+i]);
	lp2 := LPolynomial(Eell2);
	t2 := -Coefficient(lp2, 1);
	assert t1 eq t2;

	return t1;
end function;



/*
The next function returns the coefficient a_\ell of the i-th newform
*/
function a_ell(ell, i)
	if i le 2 then
		return TraceOfFrobenius(ChangeRing(Es[i], GF(ell)));
	else
		return FastCoefficientIrrationalNewform(ell);
	end if;
end function;



/*
The next block of code tests that our fast method to compute the
coefficients of the G_i via point counting on elliptic curves
returns the correct result for all primes up to 10^4.
The creation of the space of newforms require CHIMP (https://github.com/edgarcosta/CHIMP)

chi := DirichletCharacter("160.1");
S:= CuspForms(chi, 2);
N := Newforms(S);
G1 := N[1][1];
G2 := N[2][1];
G3 := N[3][1];


for ell in [i : i in [7..10^4] | IsPrime(i) and i mod 4 eq 1] do
	assert Coefficient(G3, ell) eq a_ell(ell, 3);
end for;
for ell in [i : i in [7..10^4] | IsPrime(i) ] do
	assert Coefficient(G1, ell) eq a_ell(ell, 1);
end for;
for ell in [i : i in [7..10^4] | IsPrime(i) ] do
	assert Coefficient(G2, ell) eq a_ell(ell, 2);
end for;

*/

/*
The next function computes the Frobenius trace a_\ell(E_\delta)
*/
function a_ell_positivecharacteristic(ell, delta)
	GFell := GF(ell);
	E := EllipticCurve([GF(ell)!0,2*delta,0,(delta^2-D),0]);
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
for indexForm in [1..3] do
	"=== Checking form number", i, "===";
	for p in [j : j in [7..10^5] | IsPrime(j) ] do

		rPossible := {-Integers()!( (p-1)/2 )..Integers()!( (p-1)/2 )};
		n := 1;
		while not (rPossible subset {-3, 3}) do	// it suffices to rule out all values of r except these two
			ell := n*p + 1;
			if IsPrime(ell) and ( indexForm lt 3 or ell mod 4 eq 1 ) then	// for the irrational newform we only consider \ell if it is 1 modulo 4
				if LegendreSymbol(D, ell) eq 1 then
					_, theta := IsSquare(GF(ell)!D);
					if ((1+theta)/2)^n ne 1 then
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
							Rl := { GF(p)!Log(delta + theta) / GF(p)!Log( (1+theta) / 2) : delta in Xell };
							rPossible := {r : r in rPossible | GF(p)!r in Rl};
						end if;
					end if;
				end if;
			end if;
			n := n+1;
		end while;
	"Checked p =", p, ". Only possibilities remaining: r \in ", rPossible, ".";
	end for;
end for;

/*
The very fact that the script terminates implies that for every p < 10^5 we have found
a combination of auxiliary primes \ell that forces r \in {-3, +3}
*/

exit;
