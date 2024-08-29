SetLogFile("First_lower_bound_b.out");
/*
Rule out very small values of b
*/
D:= 37;

/*
The next function tries to rule out quickly
that b^p + D is a square by relying on the
fact (Chebotarev) that b^p+D is a square if
and only if it is a square modulo every prime.
If we cannot prove that b^p+D is in fact a
square, we take explicit square roots to check.
*/
function FastIsSquare(b, p)
	q := 2;
	count := 0;
	while count lt 200 do
		test := IsSquare(GF(q)!b^p+D);
		if not test then
			return false;
		end if;
		q := NextPrime(q);
		count := count + 1;
	end while;
	return IsSquare(b^p+D);
end function;


/*
If (D/b) = -1, or more generally if b has a prime
divisor q such that (D/q) = -1, then the equation
a^2 - D = b^p has no solution (a,p), because any
solution would imply that D is a square modulo
every prime divisor of b.
*/
function RapidTest(b)
	if JacobiSymbol(D, b) eq -1 then
		return false;
	end if;
	PD := PrimeDivisors(b);
	return &and[ IsSquare(GF(q)!D) : q in PD ];
end function;


/*
Main loop: we test all odd numbers up to 201
*/
for b0 in [1..100] do
	b := 2*b0 + 1;
	if RapidTest(b) then
		for p in PrimesUpTo(2100000) do
			if FastIsSquare(b,p) then
				b, p, b^p+D;
			end if;
		end for;
	end if;
end for;

exit;
