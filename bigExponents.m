/*************************************************
** MODULE NAME: bigExponents.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module treats the case where 
**              we are unable to bound the exponent with the
**              help of the modular method alone, and we 
**              therefore need to prove that there are no solutions
**              under the given LFL bounds.
**************************************************/

Attach("main.m");
import "main.m":symplecticMethod;
import "main.m":KrausMethod;
import "main.m":modularThue;

/* These are the pairs (C1, C2) in Proposition 5.2 */
coeffs := [[1,7], [1,15], [1, 23], [3,5], [3,13], [5,3], [5,11], [7,9], [7, 25], [11,5], [11,21], [13,3], [13,11], [17,15]];

/* These are the ECs associated to each of the pairs, as in Table 3.*/
ECs := ["14a1", "30a1", "46a1", "90a1", "234b1", "150a1", "550g1", "294f1", "490g1", "1210a1", "5082y1", "1014c1", "3718c1", "8670q1"];

/* These are the values of N0 given in Proposition 5.2, and proved in Section 8. */
bounds := [5.6947e8, 2.574e8, 1.7893e9, 2.574e8, 1.0512e9, 2.574e8, 7.2518e8, 5.6947e8, 5.6947e8, 7.2518e8, 1.4208e9, 1.0512e9, 2.8141e9, 8.95396e8];

for i := 1 to #coeffs do

	C1 := coeffs[i,1];
	C2 := coeffs[i,2];
	f := ModularForm(EllipticCurve(ECs[i]));
	p := 11;
	
	t := Cputime();
	while p lt bounds[i] do
	
		if not symplecticMethod(p, f, C1, C2) then
								
			if not KrausMethod(p, f, 100, C1, C2) then
									
				if not modularThue(p, f, 100, C1, C2) then
					print "The case C1=", C1, ", C2=", C2, " and p=", p, " is problematic.";
				end if;
			end if;
		end if;	
		
		print p;
		
		p := NextPrime(p);
	
	end while;
	
	print "The case C1=", C1, ", C2=", C2, " has been solved in time ", Cputime(t);

end for;
