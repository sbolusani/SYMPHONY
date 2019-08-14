/*===========================================================================*/
/*                                                                           */
/* This file is part of the SYMPHONY Branch, Cut, and Price Library.         */
/*                                                                           */
/* SYMPHONY was jointly developed by Ted Ralphs (ted@lehigh.edu) and         */
/* Laci Ladanyi (ladanyi@us.ibm.com).                                        */
/*                                                                           */
/* (c) Copyright 2000-2007 Ted Ralphs. All Rights Reserved.                  */
/*                                                                           */
/* This software is licensed under the Eclipse Public License. Please see    */
/* accompanying file for terms.                                              */
/*                                                                           */
/*===========================================================================*/

/* system include files */
#include <stdlib.h>
#include <math.h>
#include <assert.h>

/* SYMPHONY include files */
#include "sym_constants.h"
#include "sym_macros.h"
#include "sym_cg_u.h"
#include "sym_qsort.h"
#include "sym_master.h"

/* User include files */
#include "cblp.h"

/*===========================================================================*/

void generate_disjunctive_cuts(user_problem *prob, int varnum,
		   double objval, int *indices, double *values,
		   double etol, int *num_cuts, int *alloc_cuts,
		   cut_data ***cuts);

/*===========================================================================*\
 * This file contains user-written functions used by the cut generator
 * process.
\*===========================================================================*/

/*===========================================================================*\
 * Here is where the user must receive all of the data sent from
 * user_send_cg_data() and set up data structures. Note that this function is
 * only called if one of COMPILE_IN_CG, COMPILE_IN_LP, or COMPILE_IN_TM is
 * FALSE. For sequential computation, nothing is needed here.
\*===========================================================================*/

int user_receive_cg_data(void **user, int dg_id)
{
   return(USER_DEFAULT);
}

/*===========================================================================*/

/*===========================================================================*\
 * If the user wants to fill in a customized routine for sending and receiving
 * the LP solution, it can be done here. For most cases, the default routines
 * are fine.
\*===========================================================================*/

int user_receive_lp_solution_cg(void *user)
{
   return(USER_DEFAULT);
}

/*===========================================================================*/

/*===========================================================================*\
 * Find cuts violated by a particular LP solution. This can be a fairly
 * involved function but the bottom line is that an LP solution comes in
 * and cuts go out. Remember, use the function cg_send_cut() to send cuts out
 * when they are found.
\*===========================================================================*/

int user_find_cuts(void *user, int varnum, int iter_num, int level,
		   int index, double objval, int *indices, double *values,
		   double ub, double etol, int *num_cuts, int *alloc_cuts,
		   cut_data ***cuts)
{
   user_problem *prob = (user_problem *) user;

   if (prob->par.user_cuts) {
      /* Here, we add an explicit cut that doesn't have a special packed form.
         This is the easiest way to add cuts, but may be inefficient in parallel.
       */

      /* Generate and add disjunctive cuts based on complementarity conditions */
      generate_disjunctive_cuts(prob, varnum, objval, indices, values,
            etol, num_cuts, alloc_cuts, cuts);

      return(USER_SUCCESS);
   } else {
      return(USER_DEFAULT);
   }
}

/*===========================================================================*/

/*===========================================================================*\
 * Generate and add disjunctive cuts based on complementarity conditons.
\*===========================================================================*/

void generate_disjunctive_cuts(user_problem *prob, int varnum,
		   double objval, int *indices, double *values,
		   double etol, int *num_cuts, int *alloc_cuts,
		   cut_data ***cuts)
{
   aux_data *aux = &(prob->aux);

   /* Identify the maximum violated complementarity condition */
   double *rowact, *pmatval = prob->mip->matval;
   double *prhs = prob->mip->rhs;
   int *pmatind = prob->mip->matind;
   int *pmatbeg = prob->mip->matbeg;
   int *pccind = prob->ccind;
   int max_viol_vind, max_viol_cind;
   int i, j, id, violcount = 0, *violind;
   violind = (int *) malloc(varnum * ISIZE); // allocating max. memory
   double *comcond_viol;
   comcond_viol = (double *) malloc(varnum * DSIZE); // allocating max. memory

   // Computing row activity of all cons.
   rowact = (double *) calloc(prob->mip->m, DSIZE);
   for (i = 0; i < varnum; i++) {
      for (j = pmatbeg[indices[i]]; j<pmatbeg[indices[i]+1]; j++) {
         rowact[pmatind[j]] += pmatval[j] * values[i];
      }
   }

   // Computing absolute violation of all complementarity conditions (CCs)
   for (i = 0; i < varnum; i++) {
      id = indices[i];
      if (pccind[id] >= 0) {
         if (fabs(values[i]) > etol &&
               fabs(rowact[pccind[id]] - prhs[pccind[id]]) > etol){
            violind[violcount] = id;
            comcond_viol[violcount++] = fabs(values[i]) *
               fabs(rowact[pccind[id]] - prhs[pccind[id]]);
         }
      }
   }

   // Sort these violations and indices according to violations
   // Most violated cind = pccind[violind[violcount - 1]]
   // Most violated vind = violind[violcount - 1]
   qsort_di(comcond_viol, violind, violcount);
   max_viol_vind = violind[violcount - 1];
   max_viol_cind = pccind[max_viol_vind];

   /* Some data */
   int orig_rownum = prob->orig_rownum, orig_colnum = prob->orig_colnum;
   int num_lower_vars = aux->num_lower_vars;
   // number of upper level constraints
   int num_upper_cons = orig_rownum - aux->num_lower_cons;
   // number of upper level variables
   int num_upper_vars = orig_colnum - num_lower_vars;
   // # of finite first-level UBs and LBs
   int num_finite_upper_ubs = 0, num_finite_upper_lbs = 0;
   double infty = prob->infty;

   // Asserting minimization obj. sense
   assert(prob->mip->obj_sense >= 0);
   assert(aux->sense_lower_obj >= 0);

   /* Create a cut-generating LP (CGLP) for obtaining coefficients for
      a disjunctive cut
   */
   sym_environment *env = sym_open_environment();
   int n = 0, m = 0, num_upper_eq_cons = 0, num_lower_eq_cons = 0, counter;
   int *matbeg, *matind;
   double *lb, *ub, *obj, *rngval, *rhs, *matval;
   char *sense;
   char *psense = prob->mip->sense;
   double *plb = prob->mip->lb;
   double *pub = prob->mip->ub;

   // Finding # of original eq. cons.
   for (i = 0; i < num_upper_cons; i++) {
      if (psense[i] == 'E') {
         num_upper_eq_cons += 1;
      }
   }
   for (i = num_upper_cons; i < orig_rownum; i++) {
      if (psense[i] == 'E') {
         num_lower_eq_cons += 1;
      }
   }

   /* Number of variables in CGLP */
   // # of cons. in the current single-level version of the CBLP
   n = prob->mip->m;
   // Doubling # of upper and lower eq. cons. to change them into ineq. cons
   n += num_upper_eq_cons + num_lower_eq_cons;
   // Doubling # of original equality dual cons. to change them into ineq. cons
   n += num_lower_vars;
   // # of cons. corresponding to bounds second-level dual vars.
   n += prob->mip->n - orig_colnum;
   // # of cons. corresponding to finite bounds on first-level vars.
   for (i = 0; i < num_upper_vars; i++) {
      if (!prob->infubind[i]) {
         num_finite_upper_ubs += 1;
      }
      if (!prob->inflbind[i]) {
         num_finite_upper_lbs += 1;
      }
   }
   n += num_finite_upper_ubs + num_finite_upper_lbs;
   // One additional var. for complementarity condition
   n += 1;
   // Doubling 'n' since we have two problems from one complementarity condition
   n *= 2;
   // vars. corresponding to obj. fn. coefs. = # of bilevel vars. + 1
   n += prob->mip->n + 1;

   /* Number of constraints in CGLP */
   // # of cons. = 2 * # of bilevel vars. + two more for RHS of disjunctive cut
   //   + one normalization constraint
   m += 2 * (prob->mip->n) + 3;

   /* Variable bounds in CGLP */
   lb = (double *) malloc(n * DSIZE);
   ub = (double *) malloc(n * DSIZE);
   counter = 0;
   // Two iterations for two disjunctive problems
   for (j = 0; j < 2; j++) {
      // Bounds corresponding to upper-level cons. + lower-level primal & dual cons.
      for (i = 0; i < prob->mip->m; i++) {
         // Original upper- and lower-level cons.
         if (psense[i] == 'E') {
            lb[counter] = -infty;
            ub[counter++] = 0;
            lb[counter] = 0;
            ub[counter++] = infty;
         } else if (psense[i] == 'L') {
            lb[counter] = -infty;
            ub[counter++] = 0;
         } else {
            lb[counter] = 0;
            ub[counter++] = infty;
         }
      }

      // Bounds corresponding to lower-level dual variable bounds
      for (i = orig_colnum; i < prob->mip->n; i++) {
         if ((plb[i] <= -infty) && (pub[i] >= infty)) {
            // Do nothing
         } else if (plb[i] <= -infty) {
            // var. <= 0
            lb[counter] = -infty;
            ub[counter++] = 0;
         } else if (pub[i] >= infty) {
            // var. >= 0
            lb[counter] = 0;
            ub[counter++] = infty;
         }
      }

      // Bounds corresponding to upper-level variable bounds
      for (i = 0; i < num_finite_upper_ubs; i++) {
         lb[counter] = -infty;
         ub[counter++] = 0;
      }
      for (i = 0; i < num_finite_upper_lbs; i++) {
         lb[counter] = 0;
         ub[counter++] = infty;
      }

      // Bounds corresponding to max. violated complementarity condition (MVCC)
      if (psense[max_viol_cind] == 'G') {
         // cons. sense is 'G' ==> MVCC sense is 'L' ==> new var. <= 0
         lb[counter] = -infty;
         ub[counter++] = 0;
      } else if (psense[max_viol_cind] == 'L') {
         // cons. sense is 'L' ==> MVCC sense is 'G' ==> new var. >= 0
         lb[counter] = 0;
         ub[counter++] = infty;
      }
   }
   // Bounds corresponding to obj. fn. coeffs. (free variables)
   for (i = 0; i < (prob->mip->n + 1); i++) {
      lb[counter] = -infty;
      ub[counter++] = infty;
   }
   assert(counter == n);

   /* Objective function coefficients in CGLP */
   obj = (double *) calloc(n, DSIZE);
   counter = n - (prob->mip->n + 1);
   // Coeffs. from the LP solution
   for (i = 0; i < varnum; i++) {
      obj[counter + indices[i]] = values[i];
   }
   // Coeff. of last variable
   obj[n - 1] = -1.0;

   /* Row sense in CGLP */
   sense = (char *) malloc(m * CSIZE);
   counter = 0;
   for (j = 0; j < 2; j++) {
      for (i = 0; i < prob->mip->n; i++) {
         sense[counter++] = 'E';
      }
      sense[counter++] = 'G';
   }
   sense[counter] = 'E';
   assert(counter == (m-1));

   /* Range values in CGLP */
   rngval = (double *) calloc(m, DSIZE);

   /* RHS values in CGLP */
   rhs = (double *) calloc(m, DSIZE);
   rhs[m - 1] = 1;

   /* Constraint matrix coefficients */
   // Building a CoinPackedMatrix of col-ordered bilevel mip matrix
   int *bilevelMatLen = (int *) malloc(n * ISIZE);
   for (i = 0; i < prob->mip->n; i++) {
      bilevelMatLen[i] = pmatbeg[i+1] - pmatbeg[i];
   }
   CoinPackedMatrix *bilevelMip = new CoinPackedMatrix(true, prob->mip->m,
         prob->mip->n, pmatbeg[prob->mip->n],
         pmatval, pmatind,
         pmatbeg, bilevelMatLen);
   // Converting col-ordering to row-ordering
   bilevelMip->reverseOrdering();

   // Build a new row-ordered matrix and RHS with all common cons. in the two
   //   disjunctive probs.
   CoinPackedMatrix *disjMat = new CoinPackedMatrix(false, 0.0, 0.0);
   double *disjRhs_val;
   int max_size = 2*prob->mip->m + (prob->mip->n - orig_colnum) +
      2*num_upper_vars + 1;
   int disjRhs_size = 0, *disjRhs_ind, num_disjMat_rows = 0;
   disjRhs_val  = (double *) malloc(max_size * DSIZE);
   disjRhs_ind  = (int *) malloc(max_size * ISIZE);

   assert(bilevelMip->getMajorDim() == prob->mip->m);

   // Adding bilevel rows to disjMat
   for (i = 0; i < prob->mip->m; i++) {
      CoinShallowPackedVector singleRow = bilevelMip->getVector(i);
      if (psense[i] == 'E') {
         disjMat->appendRow(singleRow.getNumElements(),
               singleRow.getIndices(), singleRow.getElements());
         num_disjMat_rows++;
         disjRhs_val[disjRhs_size] = prhs[i];
         disjRhs_ind[disjRhs_size] = disjRhs_size;
         disjRhs_size++;
      }
      disjMat->appendRow(singleRow.getNumElements(),
            singleRow.getIndices(), singleRow.getElements());
      num_disjMat_rows++;
      disjRhs_val[disjRhs_size] = prhs[i];
      disjRhs_ind[disjRhs_size] = disjRhs_size;
      disjRhs_size++;
   }

   // Adding lower-level dual col. bounds as rows to disjMat
   int row_size = 1, row_ind;
   double row_val = 1.0;
   for (i = orig_colnum; i < prob->mip->n; i++) {
      if ((plb[i] <= -infty) && (pub[i] >= infty)) {
         // Free variable; do nothing!
      } else {
         // Var. >= 0 or Var. <= 0
         row_ind = i;
         disjMat->appendRow(row_size, &row_ind, &row_val);
         num_disjMat_rows++;
         disjRhs_val[disjRhs_size] = 0.0;
         disjRhs_ind[disjRhs_size] = disjRhs_size;
         disjRhs_size++;
      }
   }

   // Adding upper-level col. finite UBs as rows to disjMat
   for (i = 0; i < num_upper_vars; i++) {
      if (!prob->infubind[i]) {
         row_ind = i;
         disjMat->appendRow(row_size, &row_ind, &row_val);
         num_disjMat_rows++;
         disjRhs_val[disjRhs_size] = prhs[i];
         disjRhs_ind[disjRhs_size] = disjRhs_size;
         disjRhs_size++;
      }
   }

   // Adding upper-level col. finite LBs as rows to disjMat
   for (i = 0; i < num_upper_vars; i++) {
      if (!prob->inflbind[i]) {
         row_ind = i;
         disjMat->appendRow(row_size, &row_ind, &row_val);
         num_disjMat_rows++;
         disjRhs_val[disjRhs_size] = prhs[i];
         disjRhs_ind[disjRhs_size] = disjRhs_size;
         disjRhs_size++;
      }
   }

   // Creating a copy of disjMat to be used as 2nd of the two disjunctive probs.
   CoinPackedMatrix disjMat2(*disjMat);

   // Adding variable corresponding to the MVCC to disjMat and disjRhs
   row_ind = max_viol_vind;
   disjMat->appendRow(row_size, &row_ind, &row_val);
   num_disjMat_rows++;
   disjRhs_val[disjRhs_size] = 0.0;
   disjRhs_ind[disjRhs_size] = disjRhs_size;
   disjRhs_size++;

   // Appending disjRhs to disjMat as an extra column
   disjMat->appendCol(disjRhs_size, disjRhs_ind, disjRhs_val);

   // Adding constraint corresponding to the MVCC to disjMat2
   CoinShallowPackedVector max_viol_row = disjMat2.getVector(max_viol_cind);
   disjMat2.appendRow(max_viol_row.getNumElements(),
         max_viol_row.getIndices(), max_viol_row.getElements());

   // Modifying and appending disjRhs to distMat2 as an extra column
   disjRhs_val[disjRhs_size - 1] = prhs[max_viol_cind];
   disjMat2.appendCol(disjRhs_size, disjRhs_ind, disjRhs_val);

   // Create a matrix of all zeroes
   int *zeroMat_starts, *zeroMat_lens;
   zeroMat_starts = (int *) calloc(num_disjMat_rows + 1, ISIZE);
   zeroMat_lens = (int *) calloc(num_disjMat_rows, ISIZE);
   CoinPackedMatrix *zeroMat = new CoinPackedMatrix(false, (prob->mip->n + 1),
         num_disjMat_rows, 0,
         NULL, NULL,
         zeroMat_starts, zeroMat_lens);

   // Create a copy of zeroMat
   //CoinPackedMatrix zeroMat2(*zeroMat);

   // Append zeroMat at the bottom of disjMat
   disjMat->bottomAppendPackedMatrix(*zeroMat);

   // Append disjMat2 at the bottom of zeroMat
   zeroMat->bottomAppendPackedMatrix(disjMat2);

   // At this point, useful matrices are disjMat and zeroMat

   // Create a negative identity matrix corresponding to obj. fn. coeffs. of CGLP
   double *negIdMat_elem;
   int *negIdMat_ind, *negIdMat_start, *negIdMat_len;
   negIdMat_elem = (double *) malloc((prob->mip->n + 1) * DSIZE);
   negIdMat_ind = (int *) malloc((prob->mip->n + 1) * ISIZE);
   negIdMat_start = (int *) malloc((prob->mip->n + 2) * ISIZE);
   negIdMat_len = (int *) malloc((prob->mip->n + 1) * ISIZE);
   for (i = 0; i < (prob->mip->n + 1); i++) {
      negIdMat_elem[i] = -1.0;
      negIdMat_ind[i] = i;
      negIdMat_start[i] = i;
      negIdMat_len[i] = 1;
   }
   negIdMat_start[i] = i;
   CoinPackedMatrix *negIdMat = new CoinPackedMatrix(false, (prob->mip->n + 1), (prob->mip->n + 1),
         (prob->mip->n + 1), negIdMat_elem, negIdMat_ind,
         negIdMat_start, negIdMat_len);

   // Append negIdMat to the bottom of disjMat and zeroMat
   disjMat->bottomAppendPackedMatrix(*negIdMat);
   zeroMat->bottomAppendPackedMatrix(*negIdMat);

   // Append zeroMat to the right of disjMat
   disjMat->rightAppendPackedMatrix(*zeroMat);

   // Add one last col. to disjMat corresponding to normalization con. in CGLP
   int lastCon_num_elem = 0, *lastCon_ind;
   double *lastCon_elem = 0;
   lastCon_ind = (int *) calloc(n, ISIZE);
   lastCon_elem = (double *) calloc(n, DSIZE);
   for(i = 0; i < n; i++) {
      if ((lb[i] <= -infty) && (ub[i] >= infty)) {
         // Free variables corresponding to CGLP's obj. fn. coeffs
         // So, no effect on this normalization con.
         // Assumed that no other var. is a free var. due to problem construction.
         // Do nothing!
      } else if (lb[i] <= -infty) {
         // <= 0 type variable in CGLP
         lastCon_ind[lastCon_num_elem] = i;
         lastCon_elem[lastCon_num_elem] = -1.0;
         lastCon_num_elem++;
      } else {
         // >= 0 type variable in CGLP
         lastCon_ind[lastCon_num_elem] = i;
         lastCon_elem[lastCon_num_elem] = 1.0;
         lastCon_num_elem++;
     }
   }
   disjMat->appendCol(lastCon_num_elem, lastCon_ind, lastCon_elem);

   // Now, disjMat is a row-ordered matrix whose transpose is exactly the CGLP
   //   matrix. So, get required vectors to be used for solving CGLP.
   matbeg = (int *) disjMat->getVectorStarts();
   matind = (int *) disjMat->getIndices();
   matval = (double *) disjMat->getElements();

   /* Load CGLP to SYMPHONY */
   sym_explicit_load_problem(env, n, m, matbeg, matind, matval,
         lb, ub, NULL, obj, NULL, sense, rhs, rngval, true);

   //Set SYMPHONY parameters
   sym_set_int_param(env, "verbosity", -5);
   sym_set_int_param(env, "use_symphony_application", 0);

   // Solve CGLP
   sym_solve(env);

   // obtain opt. obj. val and check if it is < 0
   double CGLP_obj_val;
   sym_get_obj_val(env, &CGLP_obj_val);

   // If obj. val. < 0, then obtain opt. sol., generate a disjunctive cut
   //   and add it to SYMPHONY MIP
   if (CGLP_obj_val <= -etol) {
      // Obtaining CGLP solution
      double *CGLP_sol;
      CGLP_sol = (double *) malloc(n * DSIZE);
      sym_get_col_solution(env, CGLP_sol);

      // Generating a disjunctive cut
      int disjCut_num_elem = 0, *disjCut_ind;
      double *disjCut_elem;
      disjCut_ind = (int *) malloc(prob->mip->n * ISIZE);
      disjCut_elem = (double *) malloc(prob->mip->n * DSIZE);
      for (i = (n - (prob->mip->n + 1)); i < (n - 1); i++) {
         // If var. value is nonzero, add it to the cut
         if (fabs(CGLP_sol[i]) > etol) {
            disjCut_ind[disjCut_num_elem] = i - (n - (prob->mip->n + 1));
            disjCut_elem[disjCut_num_elem++] = CGLP_sol[i];
         }
      }
      cg_add_explicit_cut(disjCut_num_elem, disjCut_ind, disjCut_elem,
            CGLP_sol[n-1], 0.0, 'G', TRUE, num_cuts, alloc_cuts, cuts);
   }
}

/*===========================================================================*/

/*===========================================================================*\
 * Free the user data structure. If the default setup is used with sequential
 * computation, nothing needs to be filled in here.
\*===========================================================================*/

int user_free_cg(void **user)
{
   return(USER_DEFAULT);
}

/*===========================================================================*/

/*===========================================================================*\
 * This is an undocumented (for now) debugging feature which can allow the user
 * to identify the cut which cuts off a particular known feasible solution.
\*===========================================================================*/

#ifdef CHECK_CUT_VALIDITY
int user_check_validity_of_cut(void *user, cut_data *new_cut)
{
  return(USER_DEFAULT);
}
#endif
