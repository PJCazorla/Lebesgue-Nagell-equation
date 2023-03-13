/*************************************************
** MODULE NAME: findAllSolutions.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module computes all solutions in the range that 
**              we are interested in solving. It applies all techniques
**              described in Sections 2-7, but does not deal with the case
**              where we need LFL.
**************************************************/

Attach("main.m");
import "main.m":solveForN3And4, checkSolutionsForN7, findExponents, findRootsPolynomial, generateThueYOdd;
import "main.m":generateThueYEven, preliminaryBound, imageOfInertia, quadraticTwistBound, GaloisTheoryBound;
import "main.m":symplecticMethod, KrausMethod, modularThue;

/*******************************************************************
*********** Main loops - print out all solutions *******************
*******************************************************************/

/*******************************************
************* Loop for n= 3, 4 **************
********************************************/
solutions := {};

print "---------------------------------------------------";
print "Starting to compute all solutions with n = 3, 4";
print "---------------------------------------------------";

for C1 in [1..20] do

	if IsSquarefree(C1) then 
	
		for C2 in [1..25] do
			if Gcd(C1, C2) eq 1 then
				print "Solving C1=", C1, ", C2=", C2, ", n= 3, 4 and y even";
				solutions := solutions join solveForN3And4(C1, C2);
			end if;
		end for;
		
	end if;
	
end for;

for sol in Sort(SetToSequence(solutions)) do
	print "Solution: C1 =",sol[1],", C2 =",sol[2],", x =",sol[3],", y =",sol[4],", p =",sol[5];	
end for;

/*******************************************
************* Loop for y odd  **************
********************************************/
solutions := {};

print "---------------------------------------------------";
print "Starting to compute all solutions with y odd";
print "---------------------------------------------------";

for C1 in [1..20] do

	if IsSquarefree(C1) then

		for C2 in [1..25] do
			if Gcd(C1, C2) eq 1 then
				print "Solving C1=", C1, ", C2=", C2, ", and y odd.";
				solutions := solutions join checkSolutionsForN7(C1, C2);
				primes, badprimes := findExponents(C1, C2);

				for p in primes do
					solutions := solutions join findRootsPolynomial(C1, C2, p);
				end for;
					
				for p in badprimes do
					solutions := solutions join generateThueYOdd(C1, C2, p);
				end for;
				
			end if;
		end for;
	end if;
	
end for;

for sol in Sort(SetToSequence(solutions)) do
	print "Solution: C1 =",sol[1],", C2 =",sol[2],", x =",sol[3],", y =",sol[4],", p =",sol[5];	
end for;


/*******************************************
************* Loop for y even, n=5  ******
********************************************/
solutions := {};

print "---------------------------------------------------";
print "Starting to compute all solutions with n = 5, y even";
print "---------------------------------------------------";

for C1 in [1..20] do

	if IsSquarefree(C1) then

		for C2 in [1..25] do
			if Gcd(C1, C2) eq 1 and ((C1*C2 mod 8) eq 7) then
				print "Solving C1=", C1, ", C2=", C2, ", n = 5 and y even.";
				solutions := solutions join generateThueYEven(C1, C2, 5);
			end if;
		end for;
	end if;
	
end for;

for sol in Sort(SetToSequence(solutions)) do
	print "Solution: C1 =",sol[1],", C2 =",sol[2],", x =",sol[3],", y =",sol[4],", p =",sol[5];	
end for;

/***********************************************************
*********** Loop to try to rule out existence of solutions *
*********** for y even and p >= 7. If p=7, we may need to  *
^********** solve Thue equations.   ************************
***********************************************************/ 

solutions := {};

function Rad(n) 

	ret := 1;
	
	for p in PrimeDivisors(n) do
		ret := ret*p;
	end for;
	
	return ret;

end function;

print "---------------------------------------------------";
print "Starting to compute all solutions with n > 5, y even";
print "---------------------------------------------------";

for C1 in [1..20] do

	if IsSquarefree(C1) then

		for C2 in [1..25] do
			
			if Gcd(C1, C2) eq 1 and ((C1*C2 mod 8) eq 7) then
				
				print "Solving C1=", C1, ", C2=", C2, ", n > 5 and y even.";
				NFs := Newforms(CuspForms(2*C1^2*Rad(C2)));
				
				for ff in NFs do
				
					f := ff[1];
					/* Step 1: Trying to bound the exponent for each 
					   newform */
					   
					ret := preliminaryBound(f, 100);
					if ret eq {-1} then
						ret := imageOfInertia(f, C1);
						if ret eq {-1} then
							ret := quadraticTwistBound(f, NFs, C1);
							if ret eq {-1} then
								ret := GaloisTheoryBound(f, C1, C2, 100);
							end if;
						end if;
					end if;
					   
					if ret eq {-1} then
						print "The case C1=", C1, ", C2=", C2, "and f corresponding to the EC ", CremonaReference(EllipticCurve(f)), 
						" requires separate treatment via LFL.";
					end if;
					   
					primes := ret;
					
					/* Step 2: Proving that there are no solutions for each prime. */
					
					if not(primes eq {-1}) then
						for p in primes do
							if p ge 7 then
								if not symplecticMethod(p, f, C1, C2) then
								
									if not KrausMethod(p, f, 100, C1, C2) then
									
										if not modularThue(p, f, 10, C1, C2) then
											if p gt 7 then 
												print "The case C1=", C1, ", C2=", C2, " and p=", p, " is problematic.";
											else
												print "Doing C1=", C1, ",C2=", C2, "p=7 via standard Thue equations. ";
												solutions := solutions join generateThueYEven(C1, C2, 7);
											end if;
										end if;
									end if;
								end if;
							end if;
						end for;
						
					else
						/* In this case, we rule out the case p=7, which normally is the only one 
						   susceptible to have solutions. This is merely a shortcut, and will
						   appear in Kraus's method when applied with LFL. */
						   
						if not symplecticMethod(7, f, C1, C2) then
							if not KrausMethod(7, f, 100, C1, C2) then
								if not modularThue(7, f, 10, C1, C2) then
									solutions := solutions join generateThueYEven(C1, C2, 7);
								end if;
							end if;
						end if;
					end if;
				end for;
			end if;
		end for;
	end if;
end for;

for sol in Sort(SetToSequence(solutions)) do
	print "Solution: C1 =",sol[1],", C2 =",sol[2],", x =",sol[3],", y =",sol[4],", p =",sol[5];	
end for;

