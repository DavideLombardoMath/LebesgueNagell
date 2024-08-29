/*
Checked p = 3. Only possibilities remaining: r in { -1, 0, 1 }.
Checked p = 5. Only possibilities remaining: r in { -2, -1, 1, 2 }.
Checked p = 7. Only possibilities remaining: r in { -2, -1, 0, 1, 2 }.
Checked p = 11. Only possibilities remaining: r in { -2, -1, 0, 1, 2 }.
Checked p = 13. Only possibilities remaining: r in { -4, -1, 1, 4 }.
Checked p = 17. Only possibilities remaining: r in { -8, -5, -2, -1, 0, 1, 2, 5,
8 }.
Checked p = 19. Only possibilities remaining: r in { -8, -7, -6, -3, -2, -1, 1,
2, 3, 6, 7, 8 }.
Checked p = 23. Only possibilities remaining: r in { -1, 1 }.
*/
procedure OutputEquations(D)
	SetLogFile("ThueEquations" cat IntegerToString(D) cat ".gp");
	SetAutoColumns(false);
	SetColumns(0);
	print("allocatemem(120*10^8)");

	/*
	The pairs (p, r) that we have to test. See also the output
	of the function that limits the possible values of r
	*/

	pairs := [ [3,0], [3,1], [5,1], [5,2], [7,0], [7,1], [7,2], [11, 0], [11, 1], [11, 2], [13, 1], [13, 4], [17, 0], [17, 1], [17, 2], [17, 5], [17, 8] ];


	for pair in pairs do
		p := pair[1];
		r := pair[2];
		K<sqrtD> := QuadraticField(D);
		R<u,v> := PolynomialRing(K, 2);


		if D eq 37 then
			eta := 6+sqrtD;
			etabar := 6-sqrtD;
		end if;


		f := eta^r * (u+v*(1+sqrtD)/2)^p - etabar^r * (u+v*(1-sqrtD)/2)^p;
		f := ChangeRing(f / (sqrtD), Integers());


		R<x> := PolynomialRing(Integers());

		phi := hom< Parent(f) -> R | [x, 1] >;
		f := phi(f);

		"print(\"Testing the triple D =", D, ", p =", p, "and r =", r, "\")";

		"t = thueinit(" cat Sprint(f) cat ");";
		"print(thue(t,2))\n\n";

		/*
		Solving some of these Thue equations in MAGMA is quite time-consuming
		T := Thue(f);
		time Solutions(T, 2);
		*/
	end for;
end procedure;

OutputEquations(37);
