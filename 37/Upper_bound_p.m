SetLogFile("Upper_bound_p.out");
/*
This function returns a lower bound on Log \overline{\pi}
Based on the inequalities Log \overline{\pi} >= 1/2 * Log(b)
and Log(b) >= Log b_0(D).
*/
function LowerBoundLogPiBar(D)
	if D eq 2 then
		return 1/2 * 234;
	end if;
	if D eq 3 then
		return 1/2 * 16.2;
	end if;
	if D eq 5 then
		return 1/2 * Log(11);
	end if;
	if D eq 37 then
		return 1/2 * Log(201);
	end if;
end function;

/*
The fundamental unit of the real quadratic field Q(Sqrt(D))
*/
function eta(D)
	if D eq 2 then
		return 1+Sqrt(2);
	end if;
	if D eq 3 then
		return 2+Sqrt(3);
	end if;
	if D eq 5 then
		return 1/2*(1+Sqrt(5));
	end if;
	if D eq 37 then
		return 6+Sqrt(37);
	end if;
end function;

/*
We have two functions of p, namely f_1(p) = p and a second one that grows
logarithmically, and we just need to find a p large enough that f_1(p) > f_2(p).
We test that the values given in the paper satisfy this inequality.
*/
function TestUpperBoundP(D, p)
	"Testing: for D =", D, "an upper bound is p <=", p;
	LowBound := LowerBoundLogPiBar(D);
	etaD := eta(D);
	c1 := Log(4*Sqrt(D)) / ( LowBound - 1/2 * Log(etaD) );
	c2 := 201.6 * (Log(p) + 0.62)^2 * Max(1, Log(etaD)) * LowBound / ( LowBound - 1/2 * Log(etaD) );
	return p ge (c1 + c2);
end function;

TestUpperBoundP(2, 24000);
TestUpperBoundP(3, 85000);
TestUpperBoundP(5, 31000);
TestUpperBoundP(37, 150000);

exit;
