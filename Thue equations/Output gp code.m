procedure OutputEquations(D)
	SetLogFile("ThueEquations" cat IntegerToString(D) cat ".gp");
	SetAutoColumns(false);
	SetColumns(0);
	print("allocatemem(120*10^8)");

	/*
	The pairs (p, r) that we have to test. For p >= 7 we know that
	it is enough to consider one value of r (specifically r=1 for
	D=2, 3 and r=3 for D=5).
	*/
	if D eq 5 then
		r0 := 3;
	else
		r0 := 1;
	end if;
	pairs := [ [3,0], [3,1], [5,0], [5,1], [5,2], [7,0], [7,1], [7,2], [7,3] ];
	pairs := pairs cat [ [p, r0] : p in [11..43] | IsPrime(p) ];

	for pair in pairs do
		p := pair[1];
		r := pair[2];
		K<sqrtD> := QuadraticField(D);
		R<u,v> := PolynomialRing(K, 2);

		if D eq 2 then
			eta := (1+sqrtD);
			etabar := (1-sqrtD);
		end if;
		if D eq 3 then
			eta := (2+sqrtD);
			etabar := (2-sqrtD);
		end if;
		if D eq 5 then
			eta := (1+sqrtD) / 2;
			etabar := (1-sqrtD) / 2;
		end if;

		/*
		Note that in all cases <1, eta> and <1, eta bar> are
		Z-basis of the ring of integers
		*/

		f := eta^r * (u+v*eta)^p - etabar^r * (u+v*etabar)^p;
		f := ChangeRing(f / (sqrtD), Integers());
		if D ne 5 then	// if D = 2 or 3 we can further divide by 2
			f := ChangeRing(ChangeRing(f,Rationals())/2, Integers());
		end if;


		R<x> := PolynomialRing(Integers());

		phi := hom< Parent(f) -> R | [x, 1] >;
		f := phi(f);

		"print(\"Testing the triple D =", D, ", p =", p, "and r =", r, "\")";
		"t = thueinit(" cat Sprint(f) cat ");";
		if D ne 5 then
			"print(thue(t,1))\n\n";
		else
			"print(thue(t,2))\n\n";
		end if;

		/*
		Solving some of these Thue equations in MAGMA is quite time-consuming
		T := Thue(f);
		time Solutions(T, 2);
		*/
	end for;
end procedure;

OutputEquations(2);
OutputEquations(3);
OutputEquations(5);
