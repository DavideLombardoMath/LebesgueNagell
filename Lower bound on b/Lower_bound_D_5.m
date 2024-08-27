SetLogFile("Lower_bound_D_5.out");

/*
The next function proves that the integer b^p+5 is not
a square without factoring it (by Chebotarev, an integer
is a square iff it is a square modulo every prime).
Note that the function will not terminate if b^p+5 were
in fact a square.
*/
function FastIsSquare(b, p)
	q := 2;
	while IsSquare(GF(q)!b^p+5) do
		q := NextPrime(q);
	end while;
	return false;
end function;


/*
The next function returns false if it can prove that the
equation y^2 - 5 = b^p has no solutions, for any prime p.
As discussed in the paper, a sufficient condition that
ensures that this equation has no solutions is that b be
divisible by any prime q such that (5/q) = -1 or by q=5.
We first test if b is divisible by small primes modulo which
5 is not a square (3, 7, 13) or by 5; then we compute the
Jacobi symbol (5/b) (if this is -1, then for some prime q|b
we have (5/q) = -1). If everything else fails, we factor
b and test if (5/q)=-1 for any prime divisor q of b.
*/
function RapidTest(b)
	if b mod 3 eq 0 then
		return false;
	end if;
	if b mod 5 eq 0 then
		return false;
	end if;
	if b mod 7 eq 0 then
		return false;
	end if;
	if b mod 13 eq 0 then
		return false;
	end if;
	if JacobiSymbol(5, b) eq -1 then
		return false;
	end if;
	PD := PrimeDivisors(b);
	return &and[ IsSquare(GF(q)!5) : q in PD ];
end function;

/*
This is the main loop. We test that for fixed value of
b with 1 < b < e^{15} and p < 10^5 the equation y^2-5 = b^p
has no integer solutions. Since we know that b is congruent
to -1 modulo 4, it suffices to loop over one fourth of the
values of b. Moreover, if RapidTest(b) returns false, the
equation doesn't have any solutions for any value of p, so
we can skip the loop over p. Note that we test all primes
up to 10^5, but given our bounds on p it would suffice to
stop at 31000.
*/

count := 0;
for b0 in [1..Ceiling(Exp(15)/4)] do
	count := count + 1;
	b := 4*b0 -1;
	if RapidTest(b) then
		for p in PrimesUpTo(10^5) do
			if FastIsSquare(b,p) then
				b, p, b^p+5;
			end if;
		end for;
	end if;
end for;

"Succesfully tested", count, "values of b";

/*
The fact that the script terminates means that all values of
b with 1 < b < exp(15) have been tested, and for no p < 10^5
does the equation y^2 - 5 = b^p have a solution.
*/

exit;