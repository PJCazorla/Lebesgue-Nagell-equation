/*************************************************
** MODULE NAME: main.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module includes all the necessary
**              functions to solve the generalised 
**              Lebesgue-Ramanujan-Nagell equation
**                  C1x^2 + C2 = y^n,
**              for C2 > 0. There are different 
**              subroutines to cover all cases, including:
**
**              - Small n (n=3,4).
**              - Y odd (primitive divisors of Lucas-Lehmer
**                sequences).
**              - Y even (modular method).
**************************************************/


/********************************************************
********* SMALL EXPONENTS (n=3,4) ***********************
********************************************************/

/******************************************************
** Name:solveForN3And4
** Description: Given the two coefficients C1, C2 in the
**              Lebesgue-Ramanujan-Nagell equation, this 
**              function returns a list of all solutions
**              (C1, C2, x, y, n), where n=3 or n=4, and
**              such that x > 0, gcd(C1x, C2, y) = 1.
**
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            
** Output: List of solutions of the equation with n=3 or n=4.
******************************************************/
function solveForN3And4(C1,C2)

	solutions := {};
	
	/* Error handling */
	assert IsSquarefree(C1) and Gcd(C1, C2) eq 1;	
	
	/* Case n = 3 */
	
	/* We find solutions by looking for integral points in 
	   the curve z^2 = t^3-C1^3*C2. */
	E := EllipticCurve([0,0,0,0,-C1^3*C2]);
	pts := IntegralPoints(E);
	
	/* For each integral point (t,z), we have to check if 
	   the corresponding (x,y) = (|z|/C1^2, t/C1) is an
	   integer pair. */
	for p in pts do

		y := p[1];
		x := p[2];
		
		x := AbsoluteValue(x/C1^2);
		y := y/C1;
		
		/* We check that the solutions satisfy our coprimality
		   condition and x > 0 */
		if IsIntegral(x) and IsIntegral(y) and x gt 0 then 
			x := Integers()!x;
			y := Integers()!y;
		    if Gcd(Gcd(C1*x, C2), y) eq 1 then
				solutions := solutions join {[C1, C2, x, y, 3]};
			end if;
		end if;
	end for;
	
	/* Case n = 4 */
	
	/* We find solutions by looking for integral points in 
	   the curve z^2 = t^3-C1^2*C2t. */
	E := EllipticCurve([0,0,0,-C1^2*C2, 0]);
	pts := IntegralPoints(E);
	
	/* For each integral point (t,z), we have to check if 
	   the corresponding (x,y) = (|z|/(C1^2*sqrt(t/C1)), 
	   +sqrt(t/C1)) is an integer pair. */
	for p in pts do 

		y := Sqrt(p[1]/C1);
		 
		if IsIntegral(y) and y gt 0 then 
			x := AbsoluteValue(p[2]/(C1^2*y));
			
			/* If both x and y are integral, we check the additional
			   constraints (x,y > 0; gcd(C1x, C2, y) = 1 */
			if IsIntegral(x) and x gt 0 then 
				x := Integers()!x;
				y := Integers()!y;
				if Gcd(Gcd(C1*x, C2), y) eq 1 then
					solutions := solutions join {[C1, C2, x, y, 4]};
				end if;
			end if;
		end if;
		
	end for;

	return solutions;

end function; 


/********************************************************
********* CASE Y ODD AND n > 3 **************************
********************************************************/

/******************************************************
** Name:findExponents
** Description: Given the two coefficients C1, C2 in the
**              Lebesgue-Ramanujan-Nagell equation, this 
**              function returns a list of all potential
**              exponents n > 3, for which there may be
**              a solution. In the case where the only
**              potential solutions with n=7 correspond to
**              y = 3, 5 or 9, n=7 is not returned.
**
**              In addition, the exponents are split in two
**              lists, depending on whether n divides the
**              class number of Q(sqrt(-C1C2)) or not. 
**
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            
** Output: Two lists of potential exponents, as follows:
**
**         - primes: Potential values of n not dividing the 
**                   class number of Q(sqrt(-C1C2)).
**
**         - badprimes: The rest of potential values of n.
******************************************************/
function findExponents(C1, C2)

	/* Since n = 5 is one of the possibilities in the theorem, 
       we include it in the potential primes. This is alternative
	   i) in the theorem. */
	primes := {5};
	
	/* All values of the exponent dividing the class number */
	badprimes := {};
	
	/* Error handling */
	assert IsSquarefree(C1) and Gcd(C1, C2) eq 1;
						
	/* We write C1C2 = d^2c. */
	c, d := Squarefree(C1*C2);
						
	P<x> := PolynomialRing(Rationals());
	K := NumberField(x^2+c);
						
	/* We compute all divisors of the class number of Q(-C1C2). 
	   This is alternative iii) in the theorem. */
	for p in PrimeDivisors(ClassNumber(K)) do
	
		if p gt 3 then
			badprimes := badprimes join {p};
		end if;
	
	end for;
				
	/* We include all prime divisors of (q-(-c/q)) for the  
	   relevant values of q (namely, q a prime dividing d and
	   not dividing 2c). This is alternative iv) in the theorem. */
	for q in PrimeDivisors(d) do
						
		if not((2*c mod q) eq 0) then
			
			D := q-LegendreSymbol(-c, q);
			
			for p in PrimeDivisors(D) do
								
				if p gt 3 then
					primes := primes join {p};
				end if;
								
			end for;
							
		end if;
						
	end for;

	/* Since all primes dividing the class number will require the
	   solution of Thue equations, we remove these from the list
	   primes. */
	primes := primes diff badprimes;
	
	return primes, badprimes;
	
end function;

/******************************************************
** Name:checkSolutionsForN7
** Description: Given the two coefficients C1, C2 in the
**              Lebesgue-Ramanujan-Nagell equation, this 
**              function returns all solutions with n=7
**              and y = 3, 5 or 9. These correspond to
**              alternative ii) in the theorem.
**
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            
** Output: Set of tuples (C1, C2, x, y, 7), where (x,y) are 
**         solutions of C1x^2+C2 = y^7 and y=3, 5, or 9.
******************************************************/
function checkSolutionsForN7(C1, C2)

	solutions := {};
	
	/* Error handling */
	assert IsSquarefree(C1) and Gcd(C1, C2) eq 1;
	
	/* We just check every possible value of y, and check whether the
	   corresponding x is integral, greater than 0 and the coprimality
	   condition is satisfied */
	   
	for y in [3,5,9] do
		x0 := Sqrt(((y^7-C2)/C1));
		if IsIntegral(x0) and x0 gt 0 and Gcd(Gcd(Integers()!x0, y), C2) eq 1 then
			solutions := solutions join {[C1, C2, Integers()!x0, y, 7]};
		end if;
	end for;

	return solutions;

end function;

/******************************************************
** Name:findRootsPolynomial
** Description: Given the two coefficients C1, C2 in the
**              Lebesgue-Ramanujan-Nagell equation and a 
**              exponent n which does not divide the class
**              number of Q(sqrt(-C1C2)), this function 
**              returns all tuples (C1, C2, x, y, n), where
**              (x,y) is a solution to the generalised
**              Lebesgue-Ramanujan-Nagell equation with y odd.
**              This function essentially constructs finitely
**              many polynomials fs(T) and obtains its roots
**              r. With r and s, we may obtain y and hence x.
**              This is case I. 
**
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            n -> A fixed exponent on the equation.
**            
** Output: Set of tuples (C1, C2, x, y, n), where (x,y) are 
**         solutions of C1x^2+C2 = y^n.
******************************************************/
function findRootsPolynomial(C1, C2, n)

	solutions := {};
	
	/* We define the quadratic field Q(-c) on which
	   we will need to work. */
	c, d := Squarefree(C1*C2);
	K<a> := QuadraticField(-c);
	
	/* Error handling */
	assert IsSquarefree(C1) and Gcd(C1, C2) eq 1;
	assert IsPrime(n) and n gt 3;
	assert not((ClassNumber(K) mod n) eq 0);
	
	P<X> := PolynomialRing(Rationals());
	Q<T> := PolynomialRing(K);
	
	/* Case 1: c is congruent to 3 modulo 4 */
	if ((-c) mod 4) eq 1 then
		
		/* For every admissible value of s, we compute the 
		   polynomial fs. */
		sValues := Divisors(2*d) cat [-a : a in Divisors(2*d)];
		
		for s in sValues do
		
			fs := ((T+s*a)^n-(T-s*a)^n)/(2*s*a);
			fs := P!fs - 2^n*d*C1^((n-1)/2)/s;
			
			/* We compute all roots, but only care about integer roots */
			roots := Roots(fs);
			roots := [Integers()!r[1] : r in roots | r[1] in Integers()];
			
			/* We reconstruct y with r and s, by considering that:
			   y = Norm((r+s*sqrt(-c))/(2*sqrt(C1))).
			   
			   With y, we may easily find x and check integrality. */
			for r in roots do
			
				y := (r^2+c*s^2)/(4*C1);
				x := Sqrt((y^n-C2)/C1);
				
				if IsIntegral(x) and IsIntegral(y) and x gt 0 then
				
					x := Integers()!x;
					y := Integers()!y;
					
					if Gcd(Gcd(C1*x, C2), y) eq 1 then 
						solutions := solutions join {[C1, C2, x, y, n]};
					end if;
				
				end if;
			end for;
		end for;	
		
	/* If c is congruent to 1 modulo 4, we do fundamentally the same thing.
	   The definition of fs differs a bit. */
	else
		sValues := Divisors(d) cat [-a: a in Divisors(d)];
		for s in sValues do
		
			fs := ((T+s*a)^n-(T-s*a)^n)/(2*s*a);
			fs := P!fs - d*C1^((n-1)/2)/s;
			
			roots := Roots(fs);
			roots := [Integers()!r[1] : r in roots | r[1] in Integers()];
			
			/* We reconstruct (x,y) as before, by taking into account that
			   y = Norm((r+s*sqrt(-c))/C1). */
			for r in roots do
			
				y := (r^2+c*s^2)/(C1);
				x := Sqrt((y^n-C2)/C1);
				
				if IsIntegral(x) and IsIntegral(y) and x gt 0 then
				
					x := Integers()!x;
					y := Integers()!y;
					
					if Gcd(Gcd(C1*x, C2), y) eq 1 then
						solutions := solutions join {[C1, C2, x, y, n]};
					end if;
				
				end if;
			end for;
		end for;	
	
	end if;
	
	return solutions;

end function;

forward ruleOutThue;

/******************************************************
** Name:generateThueYOdd
** Description: Given the two coefficients C1, C2 in the
**              Lebesgue-Ramanujan-Nagell equation and a 
**              exponent n which does divide the class
**              number of Q(sqrt(-C1C2)), this function 
**              returns all tuples (C1, C2, x, y, n), where
**              (x,y) is a solution to the generalised
**              Lebesgue-Ramanujan-Nagell equation with
**              y odd. This function essentially generates 
**              Thue equations and solves them.
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            n -> A fixed exponent on the equation.
**            
** Output: Set of tuples (C1, C2, x, y, n), where (x,y) are 
**         solutions of C1x^2+C2 = y^n.
******************************************************/
function generateThueYOdd(C1, C2, n)

	solutions := {};
	c, d := Squarefree(C1*C2);
		
	/* We construct the field of interest K = Q(sqrt(-C1C2)) and
	   the associated ring of integers. */
	   
	K<a> := QuadraticField(-c);
	O := MaximalOrder(K);
	
	/* Error control */
	assert IsSquarefree(C1) and Gcd(C1, C2) eq 1;
	assert IsPrime(n) and n gt 3;
	assert ((ClassNumber(O) mod n) eq 0);
	
	/* We define several polynomial rings for technical conditions - 
	   The Thue solver requires the polynomial to have integer coefficients,
	   but in order to build the polynomials we need to be able to work with
	   polynomials in two variables over the number field K */
	P<U,V> := PolynomialRing(Rationals(), 2);
	P2<X, Y> := PolynomialRing(K, 2);
	P3<T> := PolynomialRing(Integers());
	P4 := PolynomialRing(Integers(), 2);
	
	/* We construct an ideal which is the product of all prime ideals over
	   C1 */
	fact := Factorisation(C1*O);
	
	I := 1*O;
	
	for el in fact do
		I := I*el[1];
	end for;
	
	/* We compute all class group representatives J_i to check for
	   which i we have that I*J_i^-n is a principal ideal */
  	
	reps := ClassGroupPrimeRepresentatives(O, 1*O);
	dom := Domain(reps);
	
	for el in dom do
		
		/* We check for principality of the ideal I*J_i^-n. */
		princ, gener := IsPrincipal(I*(reps(el))^(-n));
		
		if princ then
			
			/* We generate the left hand side of the Thue polynomial. In particular, we 
			   find f such that f(X, Y) = 2*d. This is slightly different depending on
			   the congruence class of c modulo 4. */
			if ((-c) mod 4) eq 1 then
				f := (gener*(X + Y*(1+a)/2)^n - Conjugate(K!gener)*(X + Y*(1-a)/2)^n)/(a);
			else
				f := (gener*(X + Y*a)^n - Conjugate(K!gener)*(X + -a*Y)^n)/(a);
			end if;
			
			f := P!f;
			coeffs := Coefficients(f);
			
			/* In order for f to have integer coefficient, we compute the smallest number
			   which makes it an integer polynomial and multiply by it */
			denominator := Lcm([Denominator(c) : c in coeffs]);
			f := P4!(denominator*f);
			
			ThueEquation := Thue(P3!Evaluate(f, [T, 1]));
			
			/* Before solving the equation, we try to prove that it has no solutions compatible with the
			   Lebesgue-Ramanujan-Nagell equation by elementary congruence methods. The expression of f2
			   (which is used to reconstruct the associated x from the solution of the Thue equation) 
			   changes slightly depending on the congruence class of c modulo 4. */
			
			if ((-c) mod 4) eq 1 then
				f2 := P!(gener*(X+Y*(1+a)/2)^n + Conjugate(K!gener)*(X+Y*(1-a)/2)^n);
			else
			    f2 := P!(gener*(X+Y*a)^n + Conjugate(K!gener)*(X-a*Y)^n);
			end if; 
			
			coeffs2 := Coefficients(f2);
			/* In order for f2 to have integer coefficient, we compute the smallest number
			   which makes it an integer polynomial and multiply by it */
			denominator2 := Lcm([Denominator(c) : c in coeffs2]);
			f2 := P4!(denominator2*f2);
			   
			ret1, ret2 := ruleOutThue(C1, C2, n, 10, -1, f2, 2*C1*denominator2, f, denominator*2*d : modular := false); 
			
			/* If we have been unsuccesful, the Thue equation could potentially have solutions, and 
			   we need to find them with the built-in Thue solver */

			if not ret1 then
				/* We solve the Thue equation with the in-built Thue solver */
				sols := Solutions(ThueEquation, denominator*2*d);
			else
				sols := [];
			end if;
			
			for solution in sols do
			
				/* We reconstruct x from the solutions of the Thue equation  */
				x := Evaluate(f2, [solution[1], solution[2]])/(2*C1*denominator);
				
				/* If x is an integer, we reconstruct y and check for all compatibility conditions */
				if IsIntegral(x) then
					
					x := Integers()!x;
					y := (C1*x^2+C2)^(1/n);
					
					if x gt 0 and IsIntegral(y) then
					
						x := Integers()!AbsoluteValue(x);
						y := Integers()!y;
						
						if Gcd(Gcd(C1*x, C2), y) eq 1 then 
							solutions := solutions join {[C1, C2, x, y, n]};
						end if;
					end if;
				end if;
			end for;
		end if;
	end for;
	
	return solutions;
	
end function;

/********************************************************
********* CASE Y EVEN AND n > 3 SMALL *******************
********************************************************/

/******************************************************
** Name:generateThueYEven
** Description: Given the two coefficients C1, C2 in the
**              Lebesgue-Ramanujan-Nagell equation and a 
**              exponent n, this function 
**              returns all tuples (C1, C2, x, y, n), where
**              (x,y) is a solution to the generalised
**              Lebesgue-Ramanujan-Nagell equation with
**              y even. This function essentially generates 
**              Thue equations and solves them.
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            n -> A fixed exponent on the equation.
**            
** Output: Set of tuples (C1, C2, x, y, n), where (x,y) are 
**         solutions of C1x^2+C2 = y^n.
******************************************************/

function generateThueYEven(C1, C2, n)

	solutions := {};
	c, d := Squarefree(C1*C2);
		
	/* We construct the field of interest K = Q(sqrt(-C1C2)) and
	   the associated ring of integers. */
	   
	K<a> := QuadraticField(-c);
	O := MaximalOrder(K);
	
	/* Error control */
	assert IsSquarefree(C1) and Gcd(C1, C2) eq 1;
	assert IsPrime(n) and n gt 3;
	
	/* We define several polynomial rings for technical conditions - 
	   The Thue solver requires the polynomial to have integer coefficients,
	   but in order to build the polynomials we need to be able to work with
	   polynomials in two variables over the number field K */
	P<U,V> := PolynomialRing(Rationals(), 2);
	P2<X, Y> := PolynomialRing(K, 2);
	P3<T> := PolynomialRing(Integers());
	P4 := PolynomialRing(Integers(), 2);
	
	/* We construct an ideal which is the product of all prime ideals over
	   C1 */
	fact := Factorisation(C1*O);
	
	pc1 := 1*O;
	
	for el in fact do
		pc1 := pc1*el[1];
	end for;
	
	/* We need to work with each of the ideals over 2 */
	fact := Factorisation(2*O);
	
	for ideal in fact do 
	
		/* We build the relevant ideal I = pc1*p2^(n-2) */
		
		I := pc1*ideal[1]^(n-2);
		
		/* We compute all class group representatives J_i to check for
		   which i we have that I*J_i^(-n) is a principal ideal */
		reps := ClassGroupPrimeRepresentatives(O, 1*O);
		dom := Domain(reps);
		
		for el in dom do
			
			/* We check for principality of the ideal I*J_i^(-n). */
			princ, gamma := IsPrincipal(I*(reps(el)^(-n)));
			
			if princ then
			
			/* We generate the right hand side of the Thue polynomial. In particular, we 
				   find f such that f(X, Y) = d */
				   
				f :=  2*gamma*(X+Y*(1+a)/2)^n;
				
				coeffsReal := [Eltseq(x)[1] : x in Coefficients(f)];
				coeffsImaginary := [Eltseq(x)[2] : x in Coefficients(f)];
				
				fReal := 0;
				fImaginary := 0;
				
				for i in [0..n] do
					fReal := fReal + coeffsReal[i+1]*X^(n-i)*Y^(i);
					fImaginary := fImaginary + coeffsImaginary[i+1]*X^(n-i)*Y^(i);
				end for;
				
				fReal := P!fReal;
				fImaginary := P!fImaginary;
				
				/* In order for both polynomials to have integer coefficients, 
				we compute the smallest number which makes it an integer polynomial and multiply by it */
				denominatorReal := Lcm([Denominator(c) : c in coeffsReal]);
				denominatorImaginary := Lcm([Denominator(c) : c in coeffsImaginary]);
				
				fReal := P4!(denominatorReal*fReal);
				fImaginary := P4!(denominatorImaginary*fImaginary);
				
				ThueEquation := Thue(P3!Evaluate(fImaginary, [T, 1]));
				
				/* Before solving the Thue equation, we try to prove that there are no 
				   solutions using elementary congruence methods. */
				ret1, ret2 := ruleOutThue(C1, C2, n, 10, -1, fReal, C1*denominatorReal, fImaginary, denominatorImaginary*d : modular := false); 
				
				if not ret1 then 
					/* If the method has been unsuccesful, we solve the equation with the
					built-in Thue solver */				   
					sols := Solutions(ThueEquation, d*denominatorImaginary);
				else
					sols := [];
				end if;
			
				for solution in sols do
					
					/* We reconstruct the associated x from the solution of the Thue equation.  */
					
					/* This is equivalent to x := Real(Evaluate(f, solution)), but this guarantees
					   that the element x will be an integer to MAGMA. */
					x := Evaluate(fReal, [solution[1], solution[2]]);
					
					x := x/(denominatorReal*C1);
					
					/* If x is an integer, we reconstruct y and check for all compatibility conditions */
					if IsIntegral(x) then
						
						x := Integers()!x;
						y := (C1*x^2+C2)^(1/n);
						
						if x gt 0 and IsIntegral(y) then
						
							x := Integers()!AbsoluteValue(x);
							y := Integers()!y;
							
							if Gcd(Gcd(C1*x, C2), y) eq 1 then 
								solutions := solutions join {[C1, C2, x, y, n]};
							end if;
						end if;
					end if;
				end for;
			
			end if;
			
		end for;
		
	end for;


	return solutions;


end function;
/********************************************************
********* CASE Y EVEN AND n > 3 BIG *********************
********************************************************/

/********************************************************
********* Methods for bounding the exponent *************
********************************************************/

/******************************************************
** Name: preliminaryBound
** Description: Given a newform f arising modulo p from the 
**              Frey curve associated to the generalised Lebesgue-Ramanujan-Nagell
**              equation, this function finds a preliminary bound for the exponent p.
**
** Arguments: f -> Newform arising mod p from F.
**            nPrimes -> Number of coefficients Bl that we want to compute
**
** Output: Set of possible values >= 7 for the exponent p. 
**         {-1} if the method is unsuccessful.
******************************************************/
function preliminaryBound(f, nPrimes)
	
	l := 2;
	N := Level(f);
	
	bound := 0;
	primes := {};
	
	for j in [1..nPrimes] do
		
		l := NextPrime(l);
		while((N mod l) eq 0) do
			l := NextPrime(l);
		end while;
		
		/* Computation of the upper and lower limits of the set Sl. */
		limit := Floor(2*Sqrt(l));
	
		/* We access the l-th coefficient of the newform */
		cl := Coefficient(f, l);	
	
		/* Construction of the set Sl and computation of the second
		part of Bl'(f), corresponding to good reduction. */
		y := 1;
		for i in [-limit..limit] do
			if (i mod 2) eq 0 then
				y := y * Norm(i - cl);
			end if;
			
		end for;
		
		/* Computation of the second part of Bl'(f), corresponding to
		bad multiplicative reduction */
		x := Norm((l+1)^2 - cl^2);
		
		/* We compute Bl(f), by multiplying by l if necessary */
		if Degree(Parent(Coefficient(f, l))) eq 1 then
			Bl := Integers()!(x*y);
		else
			Bl := Integers()!(l*x*y);
		end if;
		
		bound := Gcd(Bl, bound);
	end for;

	if bound eq 0 then
		return {-1};
	else 
		for p in PrimeDivisors(bound) do
			if p gt 5 then
				primes := primes join {p};
			end if;
		end for;
		
		return primes;
	end if;
	
end function;

/******************************************************
** Name: imageOfInertia
** Description: Given a newform f arising modulo p from the 
**              Frey curve associated to the generalised Lebesgue-Ramanujan-Nagell
**              equation and the coefficient C1 of said equation, this function
**              tries to bound p by exploiting an image of inertia argument. In 
**              particular, no prime dividing C1 may divide the denominator of 
**              the j-invariant of the elliptic curve associated to f.
**
** Arguments: f -> Newform arising mod p from F. It must be rational for this
**                 method to work.
**            C1 -> Coefficient C1 in the generalised LRN equation.
**
** Output: Set of possible values >= 7 for the exponent p. 
**         {-1} if the method is unsuccessful.
******************************************************/
function imageOfInertia(f, C1) 

	assert IsSquarefree(C1);
	
	/* We first check if the newform is rational. If not,
	   this method is inapplicable. */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	if not rational then
		return {-1};
	end if;
	
	/* We build the elliptic curve associated to f and the 
	   denominator of the j-invariant. */
	E := EllipticCurve(f);
	D := Denominator(jInvariant(E));
	
	primes := {};
	bounded := false;
	
	/* For every prime divisor of C1, we have to check if it
	   divides the denominator of the j-invariant. */
	for p in PrimeDivisors(C1) do
	
		if (D mod p) eq 0 then
			bounded := true;
			
			if p gt 5 then 
				primes := primes join {p};
			end if;
		end if;
	
	end for;

	if not bounded then
		return {-1};
	else
		return primes;
	end if;

end function;

/******************************************************
** Name: quadraticTwistBound
** Description: Given a newform f arising modulo p from the 
**              Frey curve associated to the generalised Lebesgue-Ramanujan-Nagell
**              equation, the coefficient C1 of said equation and all newforms
**              of level N = 2C1^2Rad(C2), this function aims to bound the 
**              exponent p by exploiting properties of the quadratic twist.
**              In particular, any bound will always be >= 13.
**
** Arguments: f -> Newform arising mod p from F. It must be rational for this
**                 method to work.
**            NFs -> All conjugacy classes of newforms of level N. This is only
**                   to minimise computation. 
**            C1 -> Coefficient C1 in the generalised LRN equation.
**
** Output: Set of possible values >= 7 for the exponent p. 
**         {-1} if the method is unsuccessful.
******************************************************/
function quadraticTwistBound(f, NFs, C1)

	assert IsSquarefree(C1);
	
	/* We first check if the newform is rational. If not,
	   while this method could be applicable, we get much
	   better bounds by looking at the preliminary bound. */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	if not rational then
		return {-1};
	end if;

	E := EllipticCurve(f);
	N := Conductor(E);
	
	/* Initially, our bound consists of all primes > 5 and 
	   < 17. */
	bound := false;
	primes := {7, 11, 13};

	/* In this set, we will keep all primes which arise from every
	   divisor of C1. */
	primesAux := {};
	
	/* We get a quadratic twist for each divisor l of C1. */
	for l in PrimeDivisors(C1) do
	
		
		primesl := {};
		
		/* We have to look only at those quadratic twists 
		   by d, congruent to 1 modulo 4 */
		if (l mod 4) eq 1 then
			d := l;
		else
			d := -l;
		end if;
		
		/* We construct the corresponding quadratic twist. */
		Eprime := QuadraticTwist(E, d);
		Nprime := Conductor(Eprime);
		
		/* If the conductors are different, then we are guaranteed to
		   find a good bound. */
		if not(Nprime eq N) then
			bound := true;
			
			p := 3;
			
			while (N mod p) eq 0 do
				p := NextPrime(p);
			end while;
			
			/* We have to check each newform, and try to compute the corresponding 
			   quantity to bound. */
			for newform in NFs do 
			
				/* Since the newform f' arises modulo p from the elliptic curve
				   E', we have that p divides this quantity. */
				quantity := Coefficient(newform[1], p)-TraceOfFrobenius(Eprime, p);
				
				/* This quantity may  be zero, but it will not be for all p, so if it 
				   is the case, we change p and recompute the quantity. */
				while(quantity eq 0) do 
				
					p := NextPrime(p);
					while (N mod p) eq 0 do
						p := NextPrime(p);
					end while;
				
					quantity := Coefficient(newform[1], p)-TraceOfFrobenius(Eprime, p);				
				
				end while;
				
				/* We simply add all primes >= 17 dividing the quantity. */
				for prime in PrimeDivisors(Integers()!Norm(quantity)) do
				
					if prime gt 13 then
						primesl := primesl join {p};
					end if;
				
				end for;
			
			
			end for;
				
				
		end if;
		
		/* We add the primes to the relevant list. */
		if primesAux eq {} then
			primesAux := primesl;
		else
			primesAux := primesAux meet primesl;
		end if;
	
	
	end for;
	
	if bound then
		return primes join primesAux;
	else
		return {-1};
	end if;
	
end function;

/******************************************************
** Name: GaloisTheoryBound
** Description: Given a newform f arising modulo p from the 
**              Frey curve associated to the generalised Lebesgue-Ramanujan-Nagell
**              equation, the two coefficients C1, C2 of said equation and a number 
**              of primes to try, this function aims to bound the exponent p of the
**              equation by exploiting Galois Theory arguments. 
**
** Arguments: f -> Newform arising mod p from F. It must be rational for this
**                 method to work.
**            C1, C2 -> Coefficients C1, C2 in the generalised LRN equation.
**            nPrimes -> Number of primes that we want to use to try to bound 
**                       the prime p.
**
** Output: Set of possible values >= 7 for the exponent p. 
**         {-1} if the method is unsuccessful.
******************************************************/
function GaloisTheoryBound(f, C1, C2, nPrimes)

	/* We first check if the newform is rational. If not,
	   this method is inapplicable. */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	if not rational then
		return {-1};
	end if;
	
	E := EllipticCurve(f);
	N := Conductor(E);
	
	/* Initially, we have not bounded anything and the set is 
	   empty. */
	l := 2;
	bound := 0;
	primes := {};
	
	for j in [1..nPrimes] do
	
		l := NextPrime(l);
		/* By demanding that -C1C2 is a square modulo l, we may ensure
		   that the Frey curve has full 2-torsion */
		while ((N mod l) eq 0) or (LegendreSymbol(-C1*C2, l) eq -1) do
			l := NextPrime(l);
		end while;
		
		/* Computation of corresponding Bl */
		limit := Floor(2*Sqrt(l));
	
		/* We access the l-th coefficient of the newform */
		cl := TraceOfFrobenius(E, l);	
	
		/* Construction of the set Sl and computation of the second
		part of Bl'(f), corresponding to good reduction. */
		y := 1;
		for i in [-limit..limit] do
		
			/* Note that now we may assume that the Frey curve has a
			   a point of order 2, so we may be more precise when 
			   computing the bound */
			if (i mod 4) eq ((l+1) mod 4) then
				y := y *(i - cl);
			end if;
			
		end for;
		
		/* Computation of the second part of Bl'(f), corresponding to
		bad multiplicative reduction */
		x := ((l+1)^2 - cl^2);
		
		/* We compute Bl(f), by multiplying by l if necessary */
		Bl := Integers()!(x*y);
		
		bound := Gcd(Bl, bound);
		
	end for;

	if bound eq 0 then
		return {-1};
	else 
		for p in PrimeDivisors(bound) do
			if p gt 5 then
				primes := primes join {p};
			end if;
		end for;
		
		return primes;
	end if;

end function;


/********************************************************
********* Solving for specific exponents    *************
********************************************************/

/********************************************************
*** Auxiliary functions for Kraus's method and for ******
*** the combined modular-Thue                      ******
********************************************************/

/******************************************************
** Name:findModularTrace
** Description: This auxiliary function computes the Frobenius trace of the Frey curve 
**              E_{x,y} : Y^2 + XY = X^3 + (C1x-1)/4 X^2 + C1y^p/64 X, assuming that y^p
**              is a root of unity modulo l, specified by the argument r.
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            r -> Root of unity such that y^p = r mod l. We furthermore assume that 
**                 (C1x^2+C2) = r has some solutions mod. l. This is not checked.
**            l -> Prime where we want to compute the Frobenius trace.
**
** Output: The Frobenius trace of E_{x,y} at the place l.
******************************************************/
function findModularTrace(C1, C2, r, l)

	/* We find ONE value of x satisfying the equation C1x^2+C2 = r. The other one is -x,
	   and the Frey curve would be a quadratic twist of the lower one by -1 so, in particular,
	   the Frobenius trace would be \pm the one computed here. */
	x := Modsqrt((r-C2)*InverseMod(C1, l), l);
	
	/* We define the elliptic curve over Fl and compute its trace. */
	E := EllipticCurve([FiniteField(l)! 1, InverseMod(4, l)*(C1*x-1), 0, InverseMod(64, l)*(C1*r), 0]);

	return (l+1)-#E;
end function;

/******************************************************
** Name:nextValue
** Description: This auxiliary function returns the next prime of the form 
**              l = 2kp + 1, where k > 0 and p is a given prime.
**
** Arguments: l -> A prime of the form 2k'p + 1.
**            p -> A prime.
**
** Output: The next prime of the form 2kp + 1.
******************************************************/
function nextValue(l, p)

	laux := l + 2*p;

	while not(IsPrime(laux)) do
		laux := laux+2*p;
	end while;

	return laux;
	
end function;

/******************************************************
** Name:rootsOfUnity
** Description: This auxiliary function computes and returns all
**              n-th roots of unity mod l, for some even n.
**
** Further reference: None.
**
** Arguments: n -> A positive integer, which is assumed to be even.
**            l -> A positive integer, which is assumed to be prime.
**
** Output: All n-th roots of unity mod. l.
******************************************************/
function rootsOfUnity(n, l)
	
	/* We create the finite field with l elements and 
	   find a generator for its units group, which is
	   cyclic of order l-1 */
	gen := PrimitiveRoot(l);
	
	/* We find the largest integer dividing both l-1 
	   and n. This is because the element g^(l-1)/d
	   will be a generator for the corresponding 
	   subgroup of elements of order n. */
	d := Gcd(l-1, n);
	gen2 := Modexp(gen, Integers()!((l-1)/d), l);
	
	/* We compute the corresponding elements */
	
	return [Modexp(gen2, i, l) : i in [0..d-1]];
	
end function;

/******************************************************
** Name: solutionModL
** Description: This function checks whether l could be a divisor of y, i.e., if the
**              equation C1x^2 + C2 = 0 has a solution mod l. It does NOT return the solution.
**
** Arguments: l -> A prime number.
**            C1,C2 -> The two coefficients of the Lebesgue-Ramanujan-Nagell equation as above.
**
** Output: True if l could be a divisor of y.
**         False otherwise.
**         
******************************************************/

function solutionModL (l, C1, C2) 

	if l eq 2 then
		return true;
	end if;
	
	return (LegendreSymbol(-C2, l)*LegendreSymbol(C1, l) eq 1);
	
end function;

/******************************************************
** Name: solveEquation
** Description: Given the two values C1, C2 in the Lebesgue-Ramanujan-Nagell
**              equation, along with an exponent k and modulo l, this equation 
**              solves (c1x^2+c2)^k = 1 mod l. This is equivalent to solving:
**
**              c1x^2+c2 = y^p mod l, whenever l = kp+1.
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            k -> Exponent.
**            l -> Modulo of the equation.
**
** Output: List of solutions to the congruence equation, possibly empty.
******************************************************/
function solveEquation (C1, C2, k, l)
	
	if C1 mod l eq 0 then
		return [0..l-1];
	end if;
	
	roots := rootsOfUnity(k, l);
	
	L := [];
	
	for r in roots do
		if (LegendreSymbol(r-C2, l)*LegendreSymbol(C1, l) ne -1) then
			x := Modsqrt((r-C2)*InverseMod(C1, l), l);
			
			L := L cat [x];
			if not (x eq 0) then
				L := L cat [l-x];
			end if;
			
		end if;
	end for;
	
	return L;
		
end function;

/******************************************************
** Name: ruleOutThue
** Description: Given the three coefficients C1, C2, p of the
**              generalised Lebesgue-Ramanujan-Nagell equation
**              C1x^2 + C2 = y^p, along with a newform from which
**              the solution arises modulo p, this function aims
**              to prove that the system of Thue equations given 
**              by:
**
**              f2(X, Y) = rhs2*x;
**              f3(X, Y) = rhs3;
**
**              does not have any solutions which give rise to solutions
**              of the Lebesgue-Ramanujan-Nagell equation. It does this
**              by working modulo l for as many primes l as specified 
**              by the argument.
**
** Arguments: C1, C2 -> Coefficients of the equation as above.
**            p -> Fixed exponent.
**            nPrimes -> Maximum number of primes l to try.
**            newform -> Newform from which the solution arises modulo p. If modular
**                       is set to false, this is irrelevant.
**            f2, f3, rhs2, rhs3 -> Coefficients of the Thue equation as above.
**
** Parameters: modular -> Determines whether the modular information should be used or not.
**                        By default, it IS used.
**
** Output: true, l if the method is successful (and hence the Thue equation does not
**              give rise to any solution). Here, l is the prime proving that the 
**              equation does not have any solutions.
**         false, -1 if not.
******************************************************/
function ruleOutThue(C1, C2, p, nPrimes, newform, f2, rhs2, f3, rhs3 : modular := true) 

	l := 1;
				
	/* We try as many primes l as specified in the argument */
	for i in [1..nPrimes] do
				
		ruledOut := true;
		
		l := nextValue(l, p);
		
		while modular and ((C1 mod l) eq 0 or (C2 mod l) eq 0) do
			l := nextValue(l, p);
		end while;
		
		/* We need to determine all the possible values of x 
		   modulo l. */
		xValues := [];
					
		/* In order to avoid excessive computation, we compute the
           coefficient of the newform just once. */
					
		if modular then 
			cl := Coefficient(newform, l);
		end if;
		
		/* These are the values of x for which l | y. */
		if solutionModL(l, C1, C2) then
		
			if (not modular) or ((Integers()!(Norm(cl^2-4)) mod p) eq 0) then
			
				x := Modsqrt(-C2*InverseMod(C1, l), l);
							
				xValues := xValues cat [x];
				xValues := xValues cat [l-x];
			end if;
		end if;
		
		/* For every solution x to the equation (C1x^2+C2)^k = 1 mod l,
		   which is equivalent to C1x^2+C2 = y^p, we check if the congruence
		   conditions provided by the modular method are satisfied. If this is
		   indeed the case, we add x to the list of possible values. */
			
		if modular then 
			for x in solveEquation(C1, C2, Integers()!((l-1)/p), l) do
			
				E := EllipticCurve([FiniteField(l)! 1, InverseMod(4, l)*(C1*x-1), 0, InverseMod(64, l)*(C1*(C1*x^2+C2)), 0]);
				frob := l+1-#E;
				
				if (Integers()!(Norm(frob-cl)) mod p) eq 0 then
					xValues := xValues cat [x];
				end if;
				
			end for;
		else
			xValues := xValues cat solveEquation(C1, C2, Integers()!((l-1)/p), l);
		end if;
		
		/* Now that we have all potential values of x, we need to compute all solutions
		(U, V) to the congruence equation:
			f2(U, V) = rhs2*x mod l, for all admissible  values of x. 
		   Since we do not expect l to be too large, we do this simply by inspection. */
		UVValues := [];
					
		for U in [0..l-1] do
			for V in [0..l-1] do
				lhs2 := Evaluate(f2, [U, V]) mod l;
				
				if ((rhs2 mod l) eq 0) then 
					if (lhs2 mod l) eq 0 then
						UVValues := UVValues cat [[U,V]];
					end if;
				else
					if (lhs2*InverseMod(rhs2, l) mod l) in xValues then
						UVValues := UVValues cat [[U,V]];
					end if;
				end if;
				
			end for;
		end for;
			
		/* For every solution, we check if the associated equation
			f3(U,V) = rhs3 mod l 
		   is satisfied. If it is not, the Thue equation does not
		   have relevant solutions */
		for tuple in UVValues do
			if (Evaluate(f3, tuple) mod l) eq (rhs3 mod l) then
				ruledOut := false;
				break;
			end if;
		end for;
		
		if ruledOut then
			return true, l;
		end if;
				
	end for;
	
	/* If we have finished the number of tries, we have not been able to 
	   rule the existence of a solution. */
	return false, -1;
	
end function;

/*********************************************************
******************* Main functions ***********************
*********************************************************/

/******************************************************
** Name: KrausMethod
** Description: This function tries to prove that there are no solutions to the equation
**              C1x^2 + C2 = y^p for a fixed value of p. This is done by a variant of 
**              Kraus's method.
**
** Arguments: p -> Fixed prime exponent.
**            f -> Newform which arises modulo p from our Frey curve.
**            tries -> Maximum number of primes to check.
**            C1, C2 -> Coefficients of the equation as above.
**
** Output: true, l if the equation DOES NOT have any solutions.
**                 Here, l is the prime proving the non-existence of sols.
**
**         false, -1 if we are unable to prove the non-existence of sols.
**         
*******************************************************/
function KrausMethod(p, f, tries, C1, C2) 

	l := 1;
	
	/* We first determine if the newform is rational and hence arises
	from an elliptic curve. We do this mainly to speed up computations
	with the use of dedicated functions. */
	
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	
	if rational then
		E := EllipticCurve(f);
	end if;
	
	/* We do as many tries as specified in the argument. */
	for i in [0..tries-1] do
	
		/* We try the next suitable prime of the for l = 2kp+1. */
		l := nextValue(l, p);
		
		while (C1 mod l) eq 0 or (C2 mod l) eq 0 do
			l := nextValue(l, p);
		end while;
		
		found := true;
		
		/* We compute the relevant coefficient c_l(f) */
		if rational then 
			frob := FrobeniusTraceDirect(E, l);
		else
			frob := Coefficient(f, l);
		end if;
		
		/* Here, we are checking the conditions for l not to be a divisor of y. We need this as a 
		   first step in order to rule out that possibility. We keep a counter to make sure that 
		   we do not remain in an infinite loop. */
		if rational then 	
			
			if (Modexp(frob, 2, p) eq 4) and solutionModL(l, C1, C2) then
				found := false;
			end if;
			
		/* If the newform is irrational, the procedure is slightly more complicated, but
		   conceptually the same. */
		else
			if solutionModL(l, C1, C2) and ((Integers()!(Norm(frob^2 - 4)) mod p) eq 0) then
				found := false;
			end if;
		end if;
		
		/* We only proceed with the second part if we have already been able to 
		   guarantee that l does not divide y. Otherwise, we go back to the 
		   beginning of the loop. */
		   
		if found then
			/* We compute c_l(f)^2. In the case where the newform is rational,
		   we perform modular exponentiation to speed things up. */
			if rational then 
				frob2 := Modexp(frob, 2, p);
			else
				frob2 := frob^2;
			end if;
			
			/* We compute all relevant roots of unity for our problem. */
			roots := rootsOfUnity(Integers()!((l-1)/p), l);
			
			for r in roots do
				
				/* We only need to check those roots of unity which have a possible
				   value of x associated to them.*/
				if (LegendreSymbol(r-C2, l)*LegendreSymbol(C1, l) ne -1) then
				
					/* For the given value of r, we compute the trace of the 
					   Frey curve at the place l.*/
					modularTrace := findModularTrace(C1, C2, r, l);
					
					/* If the newform is rational, it suffices to check
					   equality modulo p.*/
					if rational then 
						if Modexp(modularTrace, 2, p) eq frob2 then
							found := false;
							break;
						end if;
						
					/* If the newform is irrational, again the same procedure
					   works, but now we need to check that the norm is not
					   divisible by p.*/
					else
						if ((Integers()!(Norm(frob2-modularTrace^2)) mod p) eq 0) then 
							found := false;
							break;
						end if;
					end if;
				end if;
			end for;
		end if;

		/* If none of the roots satisfy the condition, there cannot be any
		   solutions to the equation for the exponent p. We return the prime
		   l which helped realise this.*/
		if found then
			return true, l;
		end if;
	end for;
	
	/* After finishing the number of tries, we have been unable to rule out
	   the existence of a solution.*/
	return false, -1;

end function;

/******************************************************
** Name: symplecticMethod
** Description: Given a tuple (C1, C2, p) for the generalised
**              Lebesgue-Ramanujan-Nagell equation
**                C1x^2+C2 = y^p,
**              this function applies the symplectic method to try
**              to rule out the existence of a solution arising
**              modulo p from a given newform f.
**
** Arguments: p -> A fixed exponent, which is assumed to be a prime.
**            f -> Newform arising mod p from F. It must be rational for this
**                 method to work.
**            C1, C2 -> Coefficients C1, C2 in the generalised LRN equation.
**
** Output: true if the symplectic method guarantees that there are no solutions.
**         false if it is not applicable or fails to guarantee the non-existence
**               of solutions.
******************************************************/
function symplecticMethod(p, f, C1, C2)

	/* Sanity checks on the arguments. */
	assert IsPrime(p);
	assert IsSquarefree(C1);
	assert Gcd(C1, C2) eq 1;

	/* We first check if the newform is rational. If not,
	   this method is inapplicable. */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	if not rational then
		return false;
	end if;
	
	/* We construct the associated elliptic curve. We know that 
	   the primes of multiplicative reduction are 2 and those primes 
	   l dividing C2. */
	E := EllipticCurve(f);
	Delta := Discriminant(MinimalModel(E));
	
	v2 := Valuation(Delta, 2);
	
	/* We apply the symplectic method to the pair (2, l) for each 
	   prime l dividing C2 */
	for l in PrimeDivisors(C2) do
	
		vl := Valuation(Delta, l);
		vlFrey := Valuation(C2, l);
		
		/* According to the theory of symplectic Galois representations, 
		   we have that ((2p-12)*vlFrey)/(v2*vl)) must be congruent to a 
		   square modulo p. */
		squareCandidate := -3*vlFrey*v2*vl;	
		
		/* If the candidate is a non-square, the symplectic method 
		   proves that there is no solution */
		if LegendreSymbol(squareCandidate, p) eq -1 then
			return true;
		end if;
	
	end for;
	
	return false;
end function;

/******************************************************
** Name: modularThue
** Description: Given a tuple (C1, C2, p) for the generalised
**              Lebesgue-Ramanujan-Nagell equation
**                C1x^2+C2 = y^p,
**              and a newform from arising modulo p from the Frey curve,
**              this function aims to prove that there are no solutions
**              by showing that the associated Thue equation has no solu-
**              tions compatible with the constraints of the modular method.
**
** Arguments: p -> A fixed exponent, which is assumed to be a prime > 5.
**            newform -> Newform arising mod p from F. It can be rational or irrational.
**            nPrimes -> Maximum number of primes to try in order to show that there
**                       are no solutions.
**            C1, C2 -> Coefficients C1, C2 in the generalised LRN equation.
**
** Output: true if the modular Thue method guarantees that there are no solutions.
**         false if it fails to guarantee the non-existence of solutions.
******************************************************/
function modularThue(p, newform, nPrimes, C1, C2) 
		
	c, d := Squarefree(C1*C2);
				
	/* We construct the field of interest K = Q(sqrt(-C1C2)) and
	   the associated ring of integers. */
			   
	K<a> := QuadraticField(-c);
	O := MaximalOrder(K);
			
	/* Error control */
	assert IsSquarefree(C1) and Gcd(C1, C2) eq 1;
	assert IsPrime(p) and p gt 5;
			
	/* We define several polynomial rings for technical conditions - 
   The Thue solver requires the polynomial to have integer coefficients,
   but in order to build the polynomials we need to be able to work with
   polynomials in two variables over the number field K */
	P<U,V> := PolynomialRing(Rationals(), 2);
    P2<X, Y> := PolynomialRing(K, 2);
	P3<T, S> := PolynomialRing(Integers(), 2);
			
	/* We construct an ideal which is the product of all prime ideals over
	   C1 */
	fact := Factorisation(C1*O);
			
	pc1 := 1*O;
			
	for el in fact do
		pc1 := pc1*el[1];
	end for;
			
	/* We need to work with each of the ideals over 2 */
	fact := Factorisation(2*O);
			
	for ideal in fact do 
			
		/* We build the relevant ideal I = pc1*p2^(p-2) */
			
		I := pc1*ideal[1]^(p-2);
				
		/* We compute all class group representatives J_i to check for
		   which i we have that I*J_i^(-p) is a principal ideal */
		reps := ClassGroupPrimeRepresentatives(O, 1*O);
		dom := Domain(reps);
				
		for el in dom do
					
			/* We check for principality of the ideal I*J_i^(-p). */
			princ, gamma := IsPrincipal(I*(reps(el)^(-p)));
					
			if princ then
					
				/* We generate the right hand side of the Thue polynomial. In particular, we 
						   find f such that f(X, Y) = C1*x + d*sqrt(-c) */
						   
				f :=  2*gamma*(X+Y*(1+d*a)/2)^p;
								
				coeffsReal := [Eltseq(x)[1] : x in Coefficients(f)];
				coeffsImaginary := [Eltseq(x)[2]: x in Coefficients(f)];
					
				/* We want to find two polynomials such that 
				     f2(X, Y) = rhs2*X,
					 f3(X, Y) = rhs3.
			       They correspond to the real and imaginary part of the 
				   previous polynomial f. */
				f2 := 0;
				f3 := 0;
						
				for i in [0..p] do
					f2 := f2 + coeffsReal[i+1]*X^(p-i)*Y^(i);
					f3 := f3 + coeffsImaginary[i+1]*X^(p-i)*Y^(i);
				end for;
						
				f2 := P!f2;
				f3 := P!f3;
						
				/* In order for both polys. to have integer coefficient, we compute the smallest number
				   which makes it an integer polynomial and multiply by it */
				coeffs2 := Coefficients(f2);
				denominator2 := Lcm([Denominator(c) : c in coeffs2]);
				f2 := denominator2*f2;
				f2 := P3!f2;
				
				coeffs3 := Coefficients(f3);
				denominator3 := Lcm([Denominator(c) : c in coeffs3]);
				f3 := denominator3*f3;
				f3 := P3!f3;
				
				/* At this point, we have found two polynomials such that:
					f2(X, Y) = denominator2*C1*x;
					f3(X, Y) = denominator3*d;
				*/
				ret1, ret2 := ruleOutThue(C1, C2, p, nPrimes, newform, f2, denominator2*C1, f3, denominator3*d);
				if ret1 eq false then
					return false;
				end if;
				   
			end if;
		end for;
	end for;
	
	/* If we have successfully eliminated all Thue equations, we may conclude that there 
	   are no solutions */
	return true;
end function;

