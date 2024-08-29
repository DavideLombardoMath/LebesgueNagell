SetLogFile("ReductionProcess.out");
/*
Our choice for the prime p_min for which we assume p >= p_min
*/
function pMin(D)
	return 19;
end function;

/*
An upper bound for the function c_2(D) introduced in the paper,
see the Appendix.
*/
function c2(D)
	if D eq 2 then
		return 1.77;
	end if;
	if D eq 3 then
		return 2.64;
	end if;
	if D eq 5 then
		return 0.97;
	end if;
end function;

/*
The fundamental unit of the quadratic field Q(\sqrt{D})
*/
function etaValue(D)
	if D eq 2 then
		return 1+Sqrt(2);
	end if;
	if D eq 3 then
		return 2+Sqrt(3);
	end if;
	if D eq 5 then
		return (1+Sqrt(5))/2;
	end if;
end function;

/*
A lower bound for a_{2, min}. The values are based on the inequalities
a_{2, min} >= 2 Log \overline{\pi} >= Log(b).
*/
function a2min(D)
	if D in {2, 3, 5} then
		return 400;
	end if;
	error "Not computed yet";
end function;

/*
Our choice for the parameter \rho, as a function of D
*/
function ChoiceOfRho(D)
	if D eq 2 then
		return 35;
	end if;

	if D eq 3 then
		return 35;
	end if;

	if D eq 5 then
		return 35;
	end if;
end function;

/*
The value of the exponent r, as a function of D. The results
of section 3 show that this does in fact only depend on D.
*/
function rExponent(D)
	if D in {2,3} then
		return 1;
	end if;
	if D eq 5 then
		return 3;
	end if;
end function;


procedure TableReductionProcess(D)
	/*
	Setup: we choose the parameters as in the paper,
	we compute the corresponding value of a_1, and
	we check that a_1 \leq 1.
	*/
	eta := etaValue(D);
	mu := 1;
	sigma := (1 + 2*mu - mu^2) / 2;
	rho := ChoiceOfRho(D);

	R1 := 3;
	S1 := 2;
	L := R1*S1;

	h := 2^10;
	r := rExponent(D);
	b1 := r*h;
	a1 := 2/h * (rho+1) * Log(eta) ;

	LowerBounda2 := a2min(D);
	gParam := 0.25;	// this is an upper bound for the parameter g. The strange name is due to the fact that we also have a function g.

	assert a1 le 1;

	/*
	We instantiate, based on the choice of parameters, the functions f and g of the paper.
	*/
	function f(Ktilde)
		/*
		LowerBoundRatio is a lower bound for the quantity denoted \lambda in the paper
		*/
		LowerBoundRatio := 1 - 2/(Ktilde * LowerBounda2);
		return LowerBoundRatio * Ktilde * (sigma * L-1) * Log(rho);
	end function;

	function g(Ktilde, p0)
		/*
		LowerBoundRatio is a lower bound for the quantity denoted \lambda in the paper
		*/
		LowerBoundRatio := 1 - 2/(Ktilde * LowerBounda2);
		/*
		Our chosen lower bound for p
		*/
		LowerBoundp := pMin(D);

		S2 := Ceiling( Sqrt(Ktilde * L * a1) ) ;
		S := S1 + S2 - 1;

		Term1 := 3/LowerBounda2 * (Log(Ktilde*L) + Log(LowerBounda2));
		Term2 := gParam * L * (2*Sqrt(Ktilde*L*a1) + R1/LowerBounda2*a1 + S1); 
		Term3 := ( 3/2 + Log( Sqrt(Ktilde*L/a1) + R1 /LowerBounda2 + (S-1)/(LowerBoundp*LowerBounda2) * rExponent(D)*h ) - Log( LowerBoundRatio * Ktilde) + Log(p0/2) ) * Ktilde;

		return Term1 + Term2 + Term3;
	end function;
	
	/*
	The next function implements the result of the main Corollary in Section 4.5
	*/
	function NewEstimate(Ktilde)
		/*
		We begin by checking assumptions 1 and 2 of the Corollary
		*/
		S2 := Ceiling( Sqrt(Ktilde * L * a1) ) ;
		S := S1 + S2 - 1;
		assert L * ( Sqrt(Ktilde * L / a1) + R1 / LowerBounda2 ) lt 2 * b1;
		assert 2*b1 lt 10^4;
		assert L*S le 2 * pMin(D);
		
		/*
		Now we simply compute the maximum in the statement of the corollary.
		We can take Floor(...) since the exponent p is certainly an integer.
		*/
		delta := Log( 4 * Sqrt(D) * eta^rExponent(D) ) / LowerBounda2 + c2(D) * (rho+1) / (2 * LowerBounda2) + 10^(-40) + Log(LowerBounda2) / LowerBounda2;
		FirstUpperBound := Sqrt(Ktilde * L * (rho+1) * 2/h * Log(eta));
		SecondUpperBound := 2 * L * Ktilde * Log(rho) + 2*delta;
		return Floor(Max(FirstUpperBound, SecondUpperBound));
	end function;

	/*
	Given a bound p <= CurrentBound for the exponent of any solution of the
	Lebesgue-Nagell equation of interest, the next function finds an upper
	bound K_0 for the minimal Ktilde that satisfies
	f(Ktilde) > g(Ktilde, CurrentBound).
	Based on the value of K_0, a new upper bound is then computed by calling
	the previous function.
	*/
	function FindNextApproximation(CurrentBound)
		K0 := 0.25;

		while f(K0) le g(K0, CurrentBound) do
			K0 := K0*1.01;
		end while;
		S2 := Ceiling( Sqrt(K0 * L * a1) ) ;
		// print "S2 =", S2;
		return K0, NewEstimate(K0);
	end function;

	/*
	Finally, we run repeatedly all of the above, starting with the initial
	estimate p <= CurrentBound = 10^5. We have stronger bounds than this,
	but the reduction process converges so quickly that the initial bound
	does not matter much. We then print the results in the format of the
	tables in Section 4 of the paper.
	*/
	PrintingReals := RealField(4);

	pBound := 10^5;
	BestEstimate := pBound;
	"D =", D;
	for n in [0..4] do
		OldBestEstimate := BestEstimate;
		Ktilde0, BestEstimate := FindNextApproximation(BestEstimate);
		print n, "&", OldBestEstimate, "&", PrintingReals!Ktilde0, "&", PrintingReals!f(Ktilde0), "&", PrintingReals!g(Ktilde0, OldBestEstimate), "&", BestEstimate, "\\\\";
	end for;
end procedure;


TableReductionProcess(2);
TableReductionProcess(3);
TableReductionProcess(5);

exit;