SetLogFile("LowerBound.out");
/*
The next function tries to prove that the integer b^p+5 is
not a square without factoring it or extracting square roots
numerically (by Chebotarev, an integer is a square iff it is
a square modulo every prime).
*/
function FastIsSquare(b, p, D)
	if Abs(b) eq 1 then
		return IsSquare(b^p+D);
	end if;
	q := 2;
	testCount := 0;
	while testCount le 100 do
		q := NextPrime(q);
		test := IsSquare(GF(q)!b^p+D);
		if not test then
			return false;
		end if;
		testCount := testCount + 1;
	end while;
	return IsSquare(b^p+D);
end function;

/*
The positive fundamental unit of Q(\sqrt{D}) with
absolute value > 1, returned as a real number of
given precision.
*/
function FundamentalUnitNumeric(D, precision)
	K<sqrtD> := QuadraticField(D);
	O := MaximalOrder(K);
	G, m := UnitGroup(O);
	gen := m(G.2);
	c := Conjugates(gen : Precision := precision);
	c := c cat [1/x : x in c];
	c := c cat [-x : x in c];
	c := [x : x in c | Re(x) ge 1];
	return Re(c[1]);
end function;

/*
The relevant value of r as a function of D
*/
function rD(D)
	if D in {2,3} then
		return 1;
	end if;
	if D eq 5 then
		return 3;
	end if;
	error "Not implemented";
end function;


/*
The main function, implementing the discussion in the paper
*/
function TestbViaContinuedFractions(r, p, D)
	/*
	First we test the small solutions, corresponding to case 1
	of the discussion in the paper
	*/
	solutions := [];
	eta := FundamentalUnitNumeric(D, 10);
	x := eta^(2*r/p);
	UpperBoundy := Exp(2*r/p * Log(eta)) * Exp(1/p*2);
	UpperBoundPi := ( 16*eta^r*UpperBoundy / ( p * (x+(-1)^r) ) )^(1/(p-2));
	UpperBoundB := UpperBoundy^2 * UpperBoundPi^2;
	for b in [-Floor(UpperBoundB)..Floor(UpperBoundB)] do
		if FastIsSquare(b, p, D) then
			Append(~solutions, b);
		end if;
	end for;
	
	/*
	Next we use continued fractions to find a lower bound on b
	*/
	eta := FundamentalUnitNumeric(D, 200);
	x := Exp(2*r/p*Log(eta));
	R := Parent(x);
	tau := - ( x - (-1)^r ) / ( (x+(-1)^r) * Sqrt(R!D) );
	cf := ContinuedFraction(tau);
	/*
	We now loop over the first several convergents; the number
	of convergents is determined by the precision 200 of the
	real field in which we work.
	*/
	for i in [1..#cf] do
		uv := Convergents([ cf[j] : j in [1..i]]);
		v := uv[1][1];
		u := uv[2][1];
		b := (u^2-D*v^2)/4;
		if IsIntegral(b) then
			b := Integers()!b;
			if FastIsSquare(b, p, D) then
				Append(~solutions, b);
			end if;
		end if;
		b := (u^2-D*v^2);
		if FastIsSquare(b, p, D) then
			Append(~solutions, b);
		end if;
	end for;
	return 2 * Log(u) - Log(4*UpperBoundy), solutions;

end function;

function TestD(D)
	Solutions := {};
	GlobalLowerBound := 1000;

	for p in PrimesUpTo(10^5) do
		if p ge 5 then
			LowerBound, SolutionsFound := TestbViaContinuedFractions(rD(D), p, D);
			GlobalLowerBound := Min(GlobalLowerBound, LowerBound);
			Solutions := Solutions join { x: x in SolutionsFound | Abs(x) ne 1 };
		end if;
	end for;
	return Solutions, GlobalLowerBound;
end function;

time TestD(2);
time TestD(3);
time TestD(5);

exit;
