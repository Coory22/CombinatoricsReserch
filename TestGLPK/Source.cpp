// TestGLPK.cpp : This file contains the 'main' function. Program execution begins and ends there.
//

#include <glpk.h>
//Tools > Options > Debugging > General Output Settings > Thread Exit Messages : Off
//We're updating this with the "GLPK/exact" solver.  
//I am concerned that this solver still uses a non-rational base field.
//I wonder if another solver would be faster.
#include <stdio.h>
#include <time.h>
#include <stdlib.h>
#include <exception>
#include <math.h>
void addCondition();
int main() {
	double minEpsilon = 1.0;
	clock_t startingTimeInClocksCycles = clock();

	long n = 2 * 4;
	//We need to seed PartialInequalitiesOld with an empty list, 
	//which seemingly needs to be done in two steps:
	int NumberOfConstaintsInpartialInequalitiesOld = 0; // 400000 * 400000;
//    int lengthOfPartialInequalitiesNew = 0; // 400000 * 400000;
	int lengthOfCertificates = 0; // 1000000;
	int* PartialInequalitiesOld = NULL;
	//set memery latter come back

	//We'll want a verification that the list of inequalities we found is valid
	//That is, a collection of values {x_0, ..., x_{12}} that actually satisfy the system.
	//At this point, the certificates don't really matter, because we think we already have all of them.
	double* Certificates = (double*)malloc(sizeof(double) * 100000);

	//Each step of the algorithm will try to find where x_i + x_j is located,
	//relative to the variables 2x_1, 2x_2, ..., 2x_n.
	//To do this, it will check whether it is possible 
	//for 2x_{k - 1} <= x_i + x_j <= 2x_k for each value of k.
	//Every step, there must be at least 1 value of k that creates 
	//a valid system of equations.

	const int _arrayLowerBounds = 1;
	char constraintName[30];
	char rowName[30];
	for (int i = 0; i < n / 2; i++)
	{
		int numberOfInequalities = 0;
		for (int j = i + 1; j < n + 1; j++)
		{
			//When i + j = n, x_i + x_j = 1, so we don't need to check this case.
			if (i + j != n)
			{
				printf("i is: %d and j is %d and the length PartialInequalities is: %d\n", i, j, numberOfInequalities);
			}

			int* PartialInequalitiesNew = (int*)glp_malloc(sizeof(int), 400000 * 300);

			// k is the index of PartialInequalitiesOld list
			for (int constraint = 0; constraint <= NumberOfConstaintsInpartialInequalitiesOld; constraint++)
			{
				int constaintNumberCount = 0;
				int row = 0;
				// print(constraints)
				// create proble to maximize;
				glp_prob* lp = glp_create_prob();
				// set problem to exact calulations

				glp_set_prob_name(lp, "coloring");
				//set arrays for matrix
				int ia[500] = { 0 }; //(int*)glp_calloc(sizeof(int), 200);
				int ja[500] = { 0 };
				double coef[500] = { 0 };
				//maximize (x1-x0)*(x2-x1)*(x1-x0)*(x2-x1)*(x1-x0)
				// 
				// set first constaint to 0

				glp_add_cols(lp, n + 1 + _arrayLowerBounds);

				glp_set_col_name(lp, 0 + _arrayLowerBounds, "x0");
				glp_set_col_bnds(lp, 0 + _arrayLowerBounds, GLP_FX, 0.0, 0.0);


				//sets last constraint to 1
				glp_set_col_name(lp, n + _arrayLowerBounds, "x_n" );
				glp_set_col_bnds(lp, n + _arrayLowerBounds, GLP_FX, 1.0, 1.0);

				//Debug:
				//To guarantee that the configuration we have has non - empty interior, we force "wiggle room" of at least epsilon :
				//epsilon = 0.00001
				glp_set_obj_name(lp, "epsilon");
				glp_set_obj_coef(lp, n + 1 + _arrayLowerBounds, 1);
				glp_set_obj_dir(lp, GLP_MAX);
				
				// add antisymetry conditions

				for (int l = 1; l < (n / 2); l++) {
					glp_add_rows(lp, 1);
					sprintf_s(rowName, "antisymetry%d", l);
					glp_set_row_name(lp, row + _arrayLowerBounds, rowName);
					glp_set_row_bnds(lp, row + _arrayLowerBounds, GLP_FX, 0.0, 0);

					//glp_add_cols(lp, 4);
					sprintf_s(constraintName, "x0%d", (n / 2 - l));
					glp_set_col_name(lp, (n / 2 - l) + _arrayLowerBounds, constraintName);

					sprintf_s(constraintName, "x0%d", (n / 2 + l));
					glp_set_col_name(lp, (n / 2 + l) + _arrayLowerBounds, constraintName);

					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = ((n / 2) - l) + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;//x_k
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = n + _arrayLowerBounds; coef[constaintNumberCount] = -1.0; //x_n
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = ((n / 2) + l) + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;//x_n-k
					//0<x_k + x_(n-k) - 1 <0
					constaintNumberCount++;
					++row;
				}

				//Add ordering inequalitys (where we use symetry here)
				for (int k = 0; k < n / 2; k++) {
					glp_add_rows(lp, 1);
					//Epsilon is stored as x[n + 1] because Python needs to recognize it as a variable.
					//So, x[n + 1] is the extra variable that forces inequalities to be strict.
					//Note: in the following line it isn't necessary to have epsilon because the epsilons elsewhere
					//also force these inequalities to be strict.
					//It's not clear to me whether or not it's best to keep it in here.
					//TestFeasibility.add_constraint(x[k] <= x[k + 1])
					sprintf_s(rowName, "orderingInequalities%d", k);
					glp_set_row_name(lp, row + _arrayLowerBounds, rowName);
					glp_set_row_bnds(lp, row + _arrayLowerBounds, GLP_UP, 0.0, 0);
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = k + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = n + 1 + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = k + 1 + _arrayLowerBounds; coef[constaintNumberCount] = -1.0;
					printf("\n%d %d\n", ja[constaintNumberCount], row);
					constaintNumberCount++;
					row++;

				}

				//Now, we'll add the partial constrants:
				if (NULL != PartialInequalitiesOld) {
					for (int k = 0; k < NumberOfConstaintsInpartialInequalitiesOld; k++) {
						glp_add_rows(lp, 2);
						int r = glp_get_num_rows(lp);
						sprintf_s(rowName, "oldInequalitys1%d", k);
						glp_set_row_name(lp, row + _arrayLowerBounds, rowName);
						glp_set_row_bnds(lp, row + _arrayLowerBounds, GLP_UP, 0.0, 0.0);

						ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = PartialInequalitiesOld[3 * k + 2] - 1; coef[constaintNumberCount] = 2.0;
						constaintNumberCount++;
						ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = n + 1 + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;
						constaintNumberCount++;
						ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = PartialInequalitiesOld[3 * k]; coef[constaintNumberCount] = -1.0;
						constaintNumberCount++;
						ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = PartialInequalitiesOld[3 * k + 1]; coef[constaintNumberCount] = -1.0;
						constaintNumberCount++;
						row++;

						sprintf_s(rowName, "oldInequalitys2%d", k+1);
						glp_set_row_name(lp, row + _arrayLowerBounds, rowName);
						glp_set_row_bnds(lp, row + _arrayLowerBounds, GLP_UP, 0.0, 0.0);

						ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = PartialInequalitiesOld[3 * k + 2]; coef[constaintNumberCount] = -2.0;
						constaintNumberCount++;
						ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = PartialInequalitiesOld[3 * k]; coef[constaintNumberCount] = 1.0;
						constaintNumberCount++;
						ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = PartialInequalitiesOld[3 * k + 1]; coef[constaintNumberCount] = 1.0;
						constaintNumberCount++;
						ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = n + 1 + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;
						constaintNumberCount++;
						row++;
					}
				}

				//All the constraints are now loaded.Now, we'll test whether we can add x_{2k - 1} <= x_i + x_j <= x_{2k} successfully.
				for (int l = i + 1; l < j + 1; l++) {
					glp_add_rows(lp, 1);
					//we add these two constaints
					sprintf_s(rowName, "newInequalitys1%d", l);
					int r = glp_get_num_rows(lp);
					glp_set_row_name(lp, row + _arrayLowerBounds, rowName);
					glp_set_row_bnds(lp, row + _arrayLowerBounds, GLP_UP, 0.0, 0);
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = l - 1 + _arrayLowerBounds; coef[constaintNumberCount] = 2.0;
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = n + 1 + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = i + _arrayLowerBounds; coef[constaintNumberCount] = -1.0;
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = j + _arrayLowerBounds; coef[constaintNumberCount] = -1.0;
					constaintNumberCount++;
					row++;

					glp_add_rows(lp, 1);
					sprintf_s(rowName, "newInequalitys2%d", l);
					glp_set_row_name(lp, row + _arrayLowerBounds, rowName);
					glp_set_row_bnds(lp, row + _arrayLowerBounds, GLP_UP, 0.0, 0);
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = l - 1 + _arrayLowerBounds; coef[constaintNumberCount] = -2.0;
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = i + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = j + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;
					constaintNumberCount++;
					ia[constaintNumberCount] = row + _arrayLowerBounds; ja[constaintNumberCount] = n + 1 + _arrayLowerBounds; coef[constaintNumberCount] = 1.0;
					constaintNumberCount++;
					row++;
					//Now, we'll check whether there is a solution that satisfies all of these constraints.
					//MILP returns an error if there is not a solution, so we use a try statement to catch that error.
					int miniMaxDistance = -1;


					glp_load_matrix(lp, glp_get_num_rows(lp), ia, ja, coef);
					 //glp_simplex(lp, NULL);
	
					 miniMaxDistance = glp_exact(lp, NULL);
					 glp_print_sol(lp, "C:\\Users\\ryan_\\glpksol");
					//int z = glp_get_obj_val(lp);
					//float x1, x2, x3, x4, x5, x6, x7, x8, x9;
					//x1 = glp_get_col_prim(lp, 1);
					//x2 = glp_get_col_prim(lp, 2);
					//x3 = glp_get_col_prim(lp, 3);
					//x4 = glp_get_col_prim(lp, 4);
					//x5 = glp_get_col_prim(lp, 5);
					//x6 = glp_get_col_prim(lp, 6);
					//x7 = glp_get_col_prim(lp, 7);
					//x8 = glp_get_col_prim(lp, 8);
					//x9 = glp_get_col_prim(lp, 9);
					//printf("\nz = %d x1 = %d; x2 = %d; x3 = %g\n", z, x1, x2, x3);

					if (miniMaxDistance > 5.0/pow(10, 15)) {
						if (miniMaxDistance < minEpsilon) {
							minEpsilon = miniMaxDistance;
						}
						if (NumberOfConstaintsInpartialInequalitiesOld == 0) {
							PartialInequalitiesNew[(row) * 3] = i;
							PartialInequalitiesNew[(row) * 3 + 1] = j;
							PartialInequalitiesNew[(row) * 3 + 2] = l;

							NumberOfConstaintsInpartialInequalitiesOld = 3 + NumberOfConstaintsInpartialInequalitiesOld;
							if (i == n / 2 - 1 and j == n) {

							}
						}
						else {

						}

					}

					//int numconst = glp_get_num_rows(lp);
					//int* tempPartialInequalitiesOld = PartialInequalitiesOld;
					//int* tempPartialInequalitiesNew = PartialInequalitiesNew;
					//int count = 0;
					//while (!PartialInequalitiesOld) {
					//	*PartialInequalitiesOld = *PartialInequalitiesNew;
					//	PartialInequalitiesNew++;
					//	PartialInequalitiesOld++;
					//	count++;
					//}
					//numberOfInequalities = count / j;
					//PartialInequalitiesNew = tempPartialInequalitiesNew;
					//PartialInequalitiesOld = tempPartialInequalitiesOld;
					glp_delete_prob(lp);
				}
			}

			if (NULL != PartialInequalitiesOld) { free(PartialInequalitiesOld); }
			PartialInequalitiesOld = PartialInequalitiesNew;
		}
	}
	clock_t endtime = clock();
	printf("The total time elapsed: %d", (endtime - startingTimeInClocksCycles) / CLOCKS_PER_SEC);
	// free allocated memory
	free(Certificates);
}


//void addCondition(glp_prob* lp, float coef1, float coef2, double coef3, int* ia, int* ja, int* coef) {

//}

//int main()
//{
//	glp_prob* lp;
//	int ia[1 + 1000], ja[1 + 1000];
//	double ar[1 + 1000], z, x1, x2, x3;
//	lp = glp_create_prob();
//	glp_set_prob_name(lp, "sample");
//	glp_set_obj_dir(lp, GLP_MAX);
//	glp_add_rows(lp, 3);
//	glp_set_row_name(lp, 1, "p");
//	glp_set_row_bnds(lp, 1, GLP_UP, 0.0, 100.0);
//	glp_set_row_name(lp, 2, "q");
//	glp_set_row_bnds(lp, 2, GLP_UP, 0.0, 600.0);
//	glp_set_row_name(lp, 3, "r");
//	glp_set_row_bnds(lp, 3, GLP_UP, 0.0, 300.0);
//	glp_add_cols(lp, 3);
//	glp_set_col_name(lp, 1, "x1");
//	glp_set_col_bnds(lp, 1, GLP_LO, 0.0, 0.0);
//	glp_set_obj_coef(lp, 1, 10.0);
//	glp_set_col_name(lp, 2, "x2");
//	glp_set_col_bnds(lp, 2, GLP_LO, 0.0, 0.0);
//	glp_set_obj_coef(lp, 2, 6.0);
//	glp_set_col_name(lp, 3, "x3");
//	glp_set_col_bnds(lp, 3, GLP_LO, 0.0, 0.0);
//	glp_set_obj_coef(lp, 3, 4.0);
//	ia[1] = 1, ja[1] = 1, ar[1] = 1.0; /* a[1,1] = 1 */
//	ia[2] = 1, ja[2] = 2, ar[2] = 1.0; /* a[1,2] = 1 */
//	ia[3] = 1, ja[3] = 3, ar[3] = 1.0; /* a[1,3] = 1 */
//	ia[4] = 2, ja[4] = 1, ar[4] = 10.0; /* a[2,1] = 10 */
//	ia[5] = 3, ja[5] = 1, ar[5] = 2.0; /* a[3,1] = 2 */
//	ia[6] = 2, ja[6] = 2, ar[6] = 4.0; /* a[2,2] = 4 */
//	ia[7] = 3, ja[7] = 2, ar[7] = 2.0; /* a[3,2] = 2 */
//	ia[8] = 2, ja[8] = 3, ar[8] = 5.0; /* a[2,3] = 5 */
//	ia[9] = 3, ja[9] = 3, ar[9] = 6.0; /* a[3,3] = 6 */
//	glp_load_matrix(lp, 9, ia, ja, ar);
//	glp_simplex(lp, NULL);
//	z = glp_get_obj_val(lp);
//	x1 = glp_get_col_prim(lp, 1);
//	x2 = glp_get_col_prim(lp, 2);
//	x3 = glp_get_col_prim(lp, 3);
//	printf("\nz = %g; x1 = %g; x2 = %g; x3 = %g\n", z, x1, x2, x3);
//	glp_delete_prob(lp);
//	return 0;
//}