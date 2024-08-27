SetLogFile("Lower_bound_D_3.out");
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
*/

chi := DirichletCharacter("96.1");
S:= CuspForms(chi, 2);
N := Newforms(S);
F1 := N[2][1];
F2 := N[1][1];


"Test starts";
for ell in [i : i in [7..10^4] | IsPrime(i) ] do
	assert Coefficient(F1, ell) eq a_ell(ell, 1);
end for;
for ell in [i : i in [7..10^4] | IsPrime(i) ] do
	assert Coefficient(F2, ell) eq a_ell(ell, 2);
end for;
"Test ends successfully";

/*
The list of possible values a_ell(F) as F varies
among the (two) newforms of weight 2, level 96,
and trivial Nebentypus.
*/
function aps(ell)
	return {a_ell(ell, 1), a_ell(ell, 2)};
end function;

/*
The variable Estimate will hold our lower bound.
*/
Estimate := 1;


for q in [i : i in [5..137] | IsPrime(i) and Max(PrimeDivisors(i-1)) le 43 ] do
	if LegendreSymbol(D, q) eq -1 then
		// "Testing q =", q;
		/*
		The variable Candidatesq stores the possible values of alpha modulo q
		*/
		Candidatesq := [];
		/*
		given the symmetry of the problem, it suffices to test half the values of alpha. 
		If a certain alpha is a potential candidate, so is -alpha, and conversely, because
		changing the sign of alpha acts as a quadratic twist by (-1), and the two newforms
		are also quadratic twists of each other by (-1).
		*/
		for alpha in [0..Floor(q/2)] do
			if GF(q)!alpha^2 ne D then
				Ealpha := EllipticCurve([GF(q)!0,2*alpha,0,3,0]);
				if ((q+1) - #RationalPoints(Ealpha)) in aps(q) then
					Append(~Candidatesq, alpha);
					Append(~Candidatesq, -alpha);
				end if;
			end if;
		end for;
	
		/*
		If there are only two possibilities for alpha mod q, we proceed
		*/
		if #Candidatesq eq 2 then
			assert Candidatesq eq [2, -2];	// we check that the two possibilities are the expected ones
			"b is necessarily 1 modulo", q;
			Estimate := Estimate * q;
			"Logarithmic lower bound =", Log(Estimate);
		end if;
	end if;
end for;

exit;
