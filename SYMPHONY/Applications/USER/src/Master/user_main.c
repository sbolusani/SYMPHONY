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
/*===========================================================================*/

#define CALL_FUNCTION(f) \
if ((termcode = f) < 0){                                                    \
   printf("Error detected: termcode = %i\n", termcode);                     \
   printf("Exiting...\n\n");                                                \
   exit(termcode);                                                          \
}

/*===========================================================================*\
   This file contains the main() for the master process.

   Note that, if you want to use the OSI SYMPHONY interface, you should set the
   USE_OSI_INTERFACE flag and define the COINROOT path in the SYMPHONY 
   Makefile. Otherwise, the C callable library functions will be used by 
   default. See below for the usage.
\*===========================================================================*/

#if defined(USE_OSI_INTERFACE)

#include "OsiSymSolverInterface.hpp"

int main(int argc, char **argv)
{
   OsiSymSolverInterface si;

   /* Parse the command line */
   si.parseCommandLine(argc, argv);
   
   /* Read in the problem */
   si.loadProblem();

   /* Find a priori problem bounds */
   si.findInitialBounds();

   /* Solve the problem */
   si.branchAndBound();
   
   return(0);
}

#else

/*===========================================================================*\
   For solving LO problems in parallel, following changes are required. 

   1. num_upperlevel_vars = 0 in user_load_problem.
   2. Obj = 0 in user_load_problem.
   3. Uncomment debugging info in main function to print original obj fn value.
   4. Comment maxUB/minLB code in user_read_problem function.
   5. Ensure rhs[index] in original dual variables to be original obj fn coeffs.

\*===========================================================================*/

#include "symphony.h"
#include "sym_master.h"
#include <stdlib.h>

#include "user.h"

#define USER_FUNC_ERROR -1

int user_test(sym_environment *env);

int main(int argc, char **argv)
{
   int termcode;

   /* Create a SYMPHONY environment */
   sym_environment *env = sym_open_environment();

   /* Print version info */
   sym_version();

   if (!env){
      printf("Error initializing environement\n");
      exit(0);
   }

   /* Create the data structure for storing the problem instance.*/
   user_problem *prob = (user_problem *)calloc(1, sizeof(user_problem));
   prob->mip = (MIPdesc *)calloc(1, sizeof(MIPdesc));

   CALL_FUNCTION( sym_set_user_data(env, (void *)prob) );

   CALL_FUNCTION( sym_parse_command_line(env, argc, argv) );

   CALL_FUNCTION( user_read_data(prob, prob->par.infile) );

   if (prob->par.bilevel) {

      CALL_FUNCTION( user_read_aux_data(prob, prob->par.auxfile) );
      CALL_FUNCTION( user_rearrange_mat_vec(prob) );
      CALL_FUNCTION( user_preprocess_single_level_prob(prob) );
      CALL_FUNCTION( user_generate_bilevel_problem(env, prob) );
      CALL_FUNCTION( user_preprocess_bilevel_prob(prob) );
      //TODO: Load the problem!!

   } else {
      /* For two cases:
       * (1) Read a single MPS file, consider first variable as upper-level
       *     variable, and proceed ahead for creating/solving a bilevel prob.
       * (2) Read a single MPS file, and solve an LP in parallel by changing
       *     certain parameters in the user_load_problem function.
      */
      //TODO: Remove (1) for sure, and also deal with (2) in a better way.
      CALL_FUNCTION( user_load_problem(env, prob) );

   }

   CALL_FUNCTION( sym_solve(env) );

   CALL_FUNCTION( sym_close_environment(env) );

   return(0);

}

/*===========================================================================*\
\*===========================================================================*/

int user_read_data(user_problem *prob, char *infile) {

   int j;
   CoinMpsIO mps;

   mps.messageHandler()->setLogLevel(0);
   
   mps.setInfinity(mps.getInfinity()); // TODO: What exactly is this doing here?

   if (mps.readMps(infile,"")){
      return(USER_FUNC_ERROR);
   }
   
   prob->mip->m  = mps.getNumRows();
   prob->mip->n  = mps.getNumCols();
   prob->mip->obj_sense = 1.0; // TODO: Remove this 'minimize' assumption.
   prob->infty = mps.getInfinity();

   /*
   double maxUB, minLB;
   maxUB = -prob->infty;
   minLB = prob->infty;
   */
   
   prob->mip->obj     = (double *) malloc(DSIZE * prob->mip->n);
   prob->mip->rhs     = (double *) malloc(DSIZE * prob->mip->m);
   prob->mip->sense   = (char *)   malloc(CSIZE * prob->mip->m);
   prob->mip->rngval  = (double *) malloc(DSIZE * prob->mip->m);
   prob->mip->ub      = (double *) malloc(DSIZE * prob->mip->n);
   prob->mip->lb      = (double *) malloc(DSIZE * prob->mip->n);
   prob->mip->colname = (char **)  malloc(sizeof(char *) * prob->mip->n);
   prob->mip->rowname = (char **)  malloc(sizeof(char *) * prob->mip->m);
   
   memcpy(prob->mip->obj, const_cast <double *> (mps.getObjCoefficients()),
	  DSIZE * prob->mip->n);
   memcpy(prob->mip->rhs, const_cast <double *> (mps.getRightHandSide()),
	  DSIZE * prob->mip->m);
   memcpy(prob->mip->sense, const_cast <char *> (mps.getRowSense()),
	  CSIZE * prob->mip->m);
   memcpy(prob->mip->rngval, const_cast <double *> (mps.getRowRange()),
	  DSIZE * prob->mip->m);
   memcpy(prob->mip->ub, const_cast <double *> (mps.getColUpper()),
	  DSIZE * prob->mip->n);
   memcpy(prob->mip->lb, const_cast <double *> (mps.getColLower()),
	  DSIZE * prob->mip->n);
   if (mps.integerColumns() == NULL) {
      prob->mip->is_int  = (char *) calloc(prob->mip->n, CSIZE);
   } else {
      prob->mip->is_int  = (char *) malloc(CSIZE * prob->mip->n);
      memcpy(prob->mip->is_int, const_cast <char *> (mps.integerColumns()),
            CSIZE * prob->mip->n);
   }

   // Save names
   for (j = 0; j < prob->mip->n; j++){
      prob->mip->colname[j] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(prob->mip->colname[j], mps.columnName(j), MAX_NAME_SIZE);
      prob->mip->colname[j][MAX_NAME_SIZE-1] = 0;
   }

   for (j = 0; j < prob->mip->m; j++){
      prob->mip->rowname[j] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(prob->mip->rowname[j], mps.rowName(j), MAX_NAME_SIZE);
      prob->mip->rowname[j][MAX_NAME_SIZE-1] = 0;
   }

   //user defined matind, matval, matbeg--fill as column ordered
   const CoinPackedMatrix * matrixByCol= mps.getMatrixByCol();
   
   prob->mip->matbeg = (int *) malloc(ISIZE * (prob->mip->n + 1));
   memcpy(prob->mip->matbeg, const_cast<int *>(matrixByCol->getVectorStarts()),
	  ISIZE * (prob->mip->n + 1));
   
   prob->mip->matval = (double *) malloc(DSIZE*prob->mip->matbeg[prob->mip->n]);
   prob->mip->matind = (int *)    malloc(ISIZE*prob->mip->matbeg[prob->mip->n]);
   
   memcpy(prob->mip->matval, const_cast<double *> (matrixByCol->getElements()),
	  DSIZE * prob->mip->matbeg[prob->mip->n]);
   memcpy(prob->mip->matind, const_cast<int *> (matrixByCol->getIndices()), 
	  ISIZE * prob->mip->matbeg[prob->mip->n]);

   //user defined matind_row, matval_row, matbeg_row--fill as row ordered
   const CoinPackedMatrix * matrixByRow= mps.getMatrixByRow();
   
   prob->matbeg_row = (int *) malloc(ISIZE * (prob->mip->m + 1));
   memcpy(prob->matbeg_row, const_cast<int *>(matrixByRow->getVectorStarts()),
	  ISIZE * (prob->mip->m + 1));
   
   prob->matval_row = (double *) malloc(DSIZE*prob->matbeg_row[prob->mip->m]);
   prob->matind_row = (int *)    malloc(ISIZE*prob->matbeg_row[prob->mip->m]);
   
   memcpy(prob->matval_row, const_cast<double *> (matrixByRow->getElements()),
	  DSIZE * prob->matbeg_row[prob->mip->m]);
   memcpy(prob->matind_row, const_cast<int *> (matrixByRow->getIndices()), 
	  ISIZE * prob->matbeg_row[prob->mip->m]);
  
   // A check
   for (j = 0; j < prob->mip->m; j++) {
      if (prob->mip->sense[j] == 'E') {
      } else if (prob->mip->sense[j] == 'L') {
      } else if (prob->mip->sense[j] == 'G') {
      } else {
         printf("\nUSER I/O: MPS file contains unknown constraint sense!!\n\n");
         return(USER_FUNC_ERROR);
      }
   }

   /*
   // Suresh: added this for finite bounds on vars for bilevel problems
   // find max of finite UBs and min of finite LBs
   for (j = 0; j < prob->mip->n; j++) {
      if ((prob->mip->ub[j] < prob->infty) && (prob->mip->ub[j] > maxUB)) {
         maxUB = prob->mip->ub[j];
      }
      if ((prob->mip->lb[j] > -prob->infty) && (prob->mip->lb[j] < minLB)) {
         minLB = prob->mip->lb[j];
      }
   }

   if (maxUB <= -prob->infty) {
      maxUB = 1e10;
   }
   if (minLB >= prob->infty) {
      minLB = -1e10;
   }

  // Suresh: added this for finite bounds on vars for bilevel problems
   // change infinity UBs and -infinity LBs to finite maxUB and minLB
   for (j = 0; j < prob->mip->n; j++) {
      if (prob->mip->ub[j] >= prob->infty) {
         prob->mip->ub[j] = maxUB;
      }
      if (prob->mip->lb[j] <= -prob->infty) {
         prob->mip->lb[j] = minLB;
      }
   }
   */

   return (FUNCTION_TERMINATED_NORMALLY);
}

/*===========================================================================*\
\*===========================================================================*/

int user_load_problem(sym_environment *env, user_problem *prob) {
   
   int i, j, index, index1, n, m, nz, nz_index = 0, *column_starts, *matrix_indices;
   double *matrix_values, *lb, *ub, *obj, *rhs, *rngval;
   char *sense, *is_int, obj_sense = 1.0;

   /* Find some info about bounds */
   prob->ubinfty = 0;
   prob->lbinfty = 0;
   prob->infubind     = (int *) calloc(prob->mip->n, ISIZE);
   prob->inflbind     = (int *) calloc(prob->mip->n, ISIZE);
   prob->infubsofar   = (int *) malloc(ISIZE * prob->mip->n);
   prob->inflbsofar   = (int *) malloc(ISIZE * prob->mip->n);
   // count number of infinity UBs and -infinity LBs, and also their indicators.
   for (j = 0; j < prob->mip->n; j++) {
      prob->infubsofar[j] = prob->ubinfty;
      if (prob->mip->ub[j] >= prob->infty) {
         prob->ubinfty++;
         prob->infubind[j] = 1;
      }
      prob->inflbsofar[j] = prob->lbinfty;
      if (prob->mip->lb[j] <= -prob->infty) {
         prob->lbinfty++;
         prob->inflbind[j] = 1;
      }
   }
   
   // number of upper level variables
   int num_upperlevel_vars = 1;
   // TODO: Suresh: following two names are misleading. Fix them later.
   // number of nonzeros in lower level constraint coeffs corresponding to upper level variables
   int nz_upperlevel = prob->mip->matbeg[num_upperlevel_vars];
   // number of nonzeros in lower level constraint coeffs corresponding to lower level variables
   int nz_lowerlevel = prob->mip->matbeg[prob->mip->n] - nz_upperlevel;
   // number of lower level finite upper bound constraints on variables
   int num_lowerlevel_ubcons = (prob->mip->n - num_upperlevel_vars - (prob->ubinfty - prob->infubsofar[num_upperlevel_vars]));
   // number of lower level dual variables on finite upper bound constraints
   int num_lowerlevel_dual_ubvars = num_lowerlevel_ubcons;
   // number of lower level finite lower bound constrains on variables
   int num_lowerlevel_lbcons = (prob->mip->n - num_upperlevel_vars - (prob->lbinfty - prob->inflbsofar[num_upperlevel_vars]));
   // number of lower level dual variables on finite lower bound constraints
   int num_lowerlevel_dual_lbvars = num_lowerlevel_lbcons;
   // number of nonzeros per row in lower level part of coefficient matrix
   int *nz_lowerlevel_row;

   /* set up the inital LP data */
   // Assumption: all constraints are in lower level
   n = prob->mip->n + prob->mip->m + num_lowerlevel_dual_ubvars + num_lowerlevel_dual_lbvars;
   m = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + (prob->mip->n - num_upperlevel_vars);
   nz = prob->mip->matbeg[prob->mip->n] + 2*num_lowerlevel_ubcons + 2*num_lowerlevel_lbcons + nz_lowerlevel;
   prob->colnum = n;
   prob->rownum = m;

   /* Allocate the arrays */
   column_starts  = (int *) malloc((n + 1) * ISIZE);
   matrix_indices = (int *) malloc((nz) * ISIZE);
   matrix_values  = (double *) malloc((nz) * DSIZE);
   obj            = (double *) malloc(n * DSIZE);
   lb             = (double *) malloc(n * DSIZE);
   ub             = (double *) malloc(n * DSIZE);
   rhs            = (double *) malloc(m * DSIZE);
   sense          = (char *) malloc(m * CSIZE);
   rngval         = (double *) calloc(m, DSIZE); /* TODO:Correct the assumption that this is zero always */
   is_int         = (char *) malloc(n * CSIZE);
   
   /* Fill out the appropriate data structures */
   if (prob->mip->obj_sense > 0.0) {
      for (i = 0; i < n; i++) {
         if (i < prob->mip->n) {
            obj[i] = -prob->mip->obj[i];
         } else {
            obj[i] = 0.0;
         }
      }
   } else {
      for (i = 0; i < n; i++) {
         if (i < prob->mip->n) {
            obj[i] = prob->mip->obj[i];
         } else {
            obj[i] = 0.0;
         }
      }
   }
   env->mip->colname = (char **) malloc(sizeof(char *) * n);  
   env->mip->rowname = (char **) malloc(sizeof(char *) * m);  

   /* The original upper level variables */
   for (i = 0; i < num_upperlevel_vars; i++) {
      is_int[i] = FALSE;
      ub[i] = prob->mip->ub[i];
      lb[i] = prob->mip->lb[i];
      env->mip->colname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(env->mip->colname[i], prob->mip->colname[i], MAX_NAME_SIZE);
      env->mip->colname[i][MAX_NAME_SIZE-1] = 0;
   }
   /* The original lower level variables */
   for (; i < prob->mip->n; i++) {
      is_int[i] = FALSE;
      ub[i] = prob->infty;
      lb[i] = -prob->infty;
      env->mip->colname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(env->mip->colname[i], prob->mip->colname[i], MAX_NAME_SIZE);
      env->mip->colname[i][MAX_NAME_SIZE-1] = 0;
   }
   /* The duals on original lower level constraints */
   for (;i < prob->mip->n + prob->mip->m; i++){
      is_int[i] = FALSE;
      if (prob->mip->sense[i - prob->mip->n] == 'L') {
         ub[i] = 0;
         lb[i] = -prob->infty;
      } else if (prob->mip->sense[i - prob->mip->n] == 'G') {
         ub[i] = prob->infty;
         lb[i] = 0;
      } else {
         ub[i] = prob->infty;
         lb[i] = -prob->infty;
      }
      env->mip->colname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->colname[i][0] = 'D';
      env->mip->colname[i][1] = '_';
      strncpy(env->mip->colname[i]+2, prob->mip->rowname[i - prob->mip->n],
            MAX_NAME_SIZE-2);
      env->mip->colname[i][MAX_NAME_SIZE-1] = 0;
   }
   /* The duals on lower level variable upper bound constraints */
   for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
      if (prob->mip->ub[j] >= prob->infty) {
         continue;
      }
      index = prob->mip->n + prob->mip->m + ((j - num_upperlevel_vars) - (prob->infubsofar[j] - prob->infubsofar[num_upperlevel_vars]));
      is_int[index] = FALSE;
      ub[index] = 0.0;
      lb[index] = -prob->infty;
      env->mip->colname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->colname[index][0] = 'U';
      env->mip->colname[index][1] = '_';
      strncpy(env->mip->colname[index]+2, prob->mip->colname[j],
            MAX_NAME_SIZE-2);
      env->mip->colname[index][MAX_NAME_SIZE-1] = 0;
      i++;
   }

   /* The duals on lower level variable lower bound constraints */
   for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
      if (prob->mip->lb[j] <= -prob->infty) {
         continue;
      }
      index = prob->mip->n + prob->mip->m + num_lowerlevel_dual_ubvars + ((j - num_upperlevel_vars) - (prob->inflbsofar[j] - prob->inflbsofar[num_upperlevel_vars]));
      is_int[index] = FALSE;
      ub[index] = prob->infty;
      lb[index] = 0.0;
      env->mip->colname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->colname[index][0] = 'L';
      env->mip->colname[index][1] = '_';
      strncpy(env->mip->colname[index]+2, prob->mip->colname[j],
            MAX_NAME_SIZE-2);
      env->mip->colname[index][MAX_NAME_SIZE-1] = 0;
      i++;
   }

   /* The original lower level constraints */
   for (i = 0; i < prob->mip->m; i++) {
      sense[i] = prob->mip->sense[i];
      rhs[i] = prob->mip->rhs[i];
      env->mip->rowname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(env->mip->rowname[i], prob->mip->rowname[i], MAX_NAME_SIZE);
      env->mip->rowname[i][MAX_NAME_SIZE-1] = 0;
   }
   /* The lower level upper bound constraints on variables */
   for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
      if (prob->mip->ub[j] >= prob->infty) {
         continue;
      }
      index = prob->mip->m + ((j - num_upperlevel_vars) - (prob->infubsofar[j] - prob->infubsofar[num_upperlevel_vars]));
      sense[index] = 'L';
      rhs[index] = prob->mip->ub[j];
      env->mip->rowname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->rowname[index][0] = 'U';
      env->mip->rowname[index][1] = '_';
      strncpy(env->mip->rowname[index]+2, prob->mip->colname[j],
            MAX_NAME_SIZE-2);
      env->mip->rowname[index][MAX_NAME_SIZE-1] = 0;
      i++;
   }

   /* The lower level lower bound constraints on variables */
   for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
      if (prob->mip->lb[j] <= -prob->infty) {
         continue;
      }
      index = prob->mip->m + num_lowerlevel_ubcons + ((j - num_upperlevel_vars) - (prob->inflbsofar[j] - prob->inflbsofar[num_upperlevel_vars]));
      sense[index] = 'G';
      rhs[index] = prob->mip->lb[j];
      env->mip->rowname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->rowname[index][0] = 'L';
      env->mip->rowname[index][1] = '_';
      strncpy(env->mip->rowname[index]+2, prob->mip->colname[j],
            MAX_NAME_SIZE-2);
      env->mip->rowname[index][MAX_NAME_SIZE-1] = 0;
      i++;
   }

   /* The lower level dual constraints */
   for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
      index = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + ((j - num_upperlevel_vars));
      sense[index] = 'E';
      // Suresh: zero'd rhs for debugging to check if entire code works properly
//      rhs[index] = 0;
      rhs[index] = prob->mip->obj[j];
      env->mip->rowname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->rowname[index][0] = 'E';
      env->mip->rowname[index][1] = '_';
      strncpy(env->mip->rowname[index]+2, prob->mip->colname[j],
	      MAX_NAME_SIZE-2);
      env->mip->rowname[index][MAX_NAME_SIZE-1] = 0;
      i++;
   }

   /* column sparse format entries corresponding to original upper level variables */
   column_starts[0] = 0;
   for (i = 0; i < num_upperlevel_vars; i++) {
      column_starts[i+1] = column_starts[i] + prob->mip->matbeg[i+1] - prob->mip->matbeg[i];
      if (prob->mip->matbeg[i + 1] - prob->mip->matbeg[i] > 0) {
         for (j = (prob->mip->matbeg[i]); j < (prob->mip->matbeg[i + 1]); j++) {
            matrix_values[nz_index] = prob->mip->matval[j];
            matrix_indices[nz_index] = prob->mip->matind[j];
            nz_index++;
         }
      }
   }
   /* column sparse format entries corresponding to original lower level variables */
   for (; i < prob->mip->n; i++) {
      column_starts[i+1] = column_starts[i] + prob->mip->matbeg[i+1] - prob->mip->matbeg[i] + 2 - prob->infubind[i] - prob->inflbind[i];
      if (prob->mip->matbeg[i + 1] - prob->mip->matbeg[i] > 0) {
         for (j = (prob->mip->matbeg[i]); j < (prob->mip->matbeg[i + 1]); j++) {
            matrix_values[nz_index] = prob->mip->matval[j];
            matrix_indices[nz_index] = prob->mip->matind[j];
            nz_index++;
         }
      }
      if (!prob->infubind[i]) {
         matrix_values[nz_index] = 1.0;
         matrix_indices[nz_index] = prob->mip->m + ((i - num_upperlevel_vars) - (prob->infubsofar[i] - prob->infubsofar[num_upperlevel_vars]));
         nz_index++;
      }
      if (!prob->inflbind[i]) {
         matrix_values[nz_index] = 1.0;
         matrix_indices[nz_index] = prob->mip->m + num_lowerlevel_ubcons + ((i - num_upperlevel_vars) - (prob->inflbsofar[i] - prob->inflbsofar[num_upperlevel_vars]));
         nz_index++;
      }
   }
   /* column sparse format entries corresponding to dual variables on original lower level constraints */
   // At first, find number of nonzeros per row in the lower level coefficient part of matrix
   nz_lowerlevel_row = (int *) malloc((prob->mip->m) * ISIZE);
   for (i = 0; i < prob->mip->m; i++) {
      nz_lowerlevel_row[i] = prob->matbeg_row[i+1] - prob->matbeg_row[i];
      if ((prob->matbeg_row[i+1] - prob->matbeg_row[i]) > 0) {
         for (j = prob->matbeg_row[i]; j < prob->matbeg_row[i+1]; j++) {
            if (prob->matind_row[j] < num_upperlevel_vars) {
               nz_lowerlevel_row[i]--;
            }
         }
      }
   }
   // Now update column sparse format entries as required
   index = 0;
   for (i = 0; i < prob->mip->m; i++) {
      column_starts[prob->mip->n + 1 + index] = column_starts[prob->mip->n + index] + nz_lowerlevel_row[i];
      index++;
      for (j = prob->matbeg_row[i]; j < prob->matbeg_row[i+1]; j++) {
         if (prob->matind_row[j] >= num_upperlevel_vars) {
            matrix_values[nz_index] = prob->matval_row[j];
            matrix_indices[nz_index] = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + (prob->matind_row[j] - num_upperlevel_vars);
            nz_index++;
         }
      }
   }
   /* column sparse format entries corresponding to dual variables on lower level primal UB constraints */
   for (i = num_upperlevel_vars; i < prob->mip->n; i++) {
      if (!prob->infubind[i]) {
         column_starts[prob->mip->n + 1 + index] = column_starts[prob->mip->n + index] + 1;
         index++;
         matrix_values[nz_index] = 1.0;
         matrix_indices[nz_index] = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + (i - num_upperlevel_vars);
         nz_index++;
      }
   }
   /* column sparse format entries corresponding to dual variables on lower level primal LB constraints */
   for (i = num_upperlevel_vars; i < prob->mip->n; i++) {
      if (!prob->inflbind[i]) {
         column_starts[prob->mip->n + 1 + index] = column_starts[prob->mip->n + index] + 1;
         index++;
         matrix_values[nz_index] = 1.0;
         matrix_indices[nz_index] = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + (i - num_upperlevel_vars);
         nz_index++;
      }
   }

   /* Assign memory and fill complementarity constraint indices for variables */
   prob->ccind          =   (int *) malloc(n * ISIZE);
   prob->ccnum          =   0;
   index = 0;
   index1 = 0;
   for (i = 0; i < n;) {
      if (i < prob->mip->n) {
         prob->ccind[i] = -1;
         i++;
      } else if (i < prob->mip->n + prob->mip->m) {
         if (sense[i - prob->mip->n] == 'E') {
            prob->ccind[i] = -1;
            i++;
            index1++;
         } else {
            prob->ccind[i] = index1;
            prob->ccnum++;
            i++;
            index1++;
         }
      } else {
         prob->ccind[i] = index1;
         prob->ccnum++;
         i++;
         index1++;
      }
   }

   /* Load the problem to SYMPHONY */   
   sym_explicit_load_problem(env, n, m, column_starts, matrix_indices,
			     matrix_values, lb, ub, is_int, obj, 0, sense, rhs,
			     rngval, true);

   /* Change prob->mip values to final problem values */
   prob->mip->n = n;
   prob->mip->m = m;
   prob->mip->nz = nz;
   prob->mip->obj_sense = obj_sense;

   prob->mip->obj    = (double *) realloc(prob->mip->obj, DSIZE * prob->mip->n);
   prob->mip->rhs    = (double *) realloc(prob->mip->rhs, DSIZE * prob->mip->m);
   prob->mip->sense  = (char *)   realloc(prob->mip->sense, CSIZE * prob->mip->m);
   prob->mip->rngval = (double *) realloc(prob->mip->rngval, DSIZE * prob->mip->m);
   prob->mip->ub     = (double *) realloc(prob->mip->ub, DSIZE * prob->mip->n);
   prob->mip->lb     = (double *) realloc(prob->mip->lb, DSIZE * prob->mip->n);
   prob->mip->is_int = (char *)   malloc(CSIZE * prob->mip->n);
   /* Default values for vvind, vvnum, feasible and rowact */
//   prob->mip->feasible    = USER__DO_NOT_BRANCH;
//   prob->mip->vvind       = (int *)    calloc(prob->mip->n, ISIZE);
//   prob->mip->vvnum       = 0;
//   prob->mip->rowact      = (double *) calloc(prob->mip->m, DSIZE);
   
   memcpy(prob->mip->obj, obj, DSIZE * prob->mip->n);
   memcpy(prob->mip->rhs, rhs, DSIZE * prob->mip->m);
   memcpy(prob->mip->sense, sense, CSIZE * prob->mip->m);
   memset(prob->mip->rngval, 0, sizeof(prob->mip->rngval));                     // TODO: Fix this assumption.
   memcpy(prob->mip->ub, ub, DSIZE * prob->mip->n);
   memcpy(prob->mip->lb, lb, DSIZE * prob->mip->n);
   memcpy(prob->mip->is_int, is_int, CSIZE * prob->mip->n);

   prob->mip->matbeg = (int *) realloc(prob->mip->matbeg, ISIZE * (prob->mip->n + 1));
   memcpy(prob->mip->matbeg, column_starts, ISIZE * (prob->mip->n + 1));
   
   prob->mip->matval = (double *) realloc(prob->mip->matval, DSIZE*prob->mip->matbeg[prob->mip->n]);
   prob->mip->matind = (int *)    realloc(prob->mip->matind, ISIZE*prob->mip->matbeg[prob->mip->n]);
   
   memcpy(prob->mip->matval, matrix_values, DSIZE * prob->mip->matbeg[prob->mip->n]);
   memcpy(prob->mip->matind, matrix_indices, ISIZE * prob->mip->matbeg[prob->mip->n]);

   /* TODO: Delete mat*_row vectors here? */
   FREE(column_starts);
   FREE(matrix_indices);
   FREE(matrix_values);
   FREE(lb);
   FREE(ub);
   FREE(obj);
   FREE(sense);
   FREE(rhs);
   FREE(rngval);
   FREE(is_int);
   FREE(nz_lowerlevel_row);
   /* TODO: Is it good to free infubind, inflbind, ifubsofar, inflbsofar here? */
   FREE(prob->inflbsofar);
   FREE(prob->infubsofar);
   FREE(prob->inflbind);
   FREE(prob->infubind);
   FREE(prob->matval_row);
   FREE(prob->matind_row);
   FREE(prob->matbeg_row);

   return (FUNCTION_TERMINATED_NORMALLY);
}


/*===========================================================================*\
 * TODO: Suresh - extend this function to read interdiction related aux data too!
\*===========================================================================*/

int user_read_aux_data(user_problem *prob, char *infile) {

   FILE *f;
   char line[50], key[50], value[50];
   int var_count = 0, cons_count = 0, obj_coeff_count = 0, i;
   aux_data *aux = &(prob->aux);

   if (!strcmp(infile, "")){
      printf("\nUSER I/O: No auxiliary data file specified\n\n");
      exit(1);
   }

   if ((f = fopen(infile, "r")) == NULL){
      fprintf(stderr, "USER I/O: file '%s' can't be opened\n", infile);
      exit(1);
   }

   /*This loop reads in the next line of the data file and compares it
     to the list of possible keywords to determine what data will follow.
     It then reads the data into the appropriate field and iterates */

   while(NULL != fgets(line, MAX_LINE_LENGTH, f)){
      strcpy(key, "");
      sscanf(line, "%s%s", key, value);

      if (strcmp(key, "N") == 0){
         READ_INT_PAR(aux->num_lower_vars);
         aux->index_lower_vars = (int *) malloc (aux->num_lower_vars * sizeof(int));
         aux->coeff_lower_obj = (double *) calloc (aux->num_lower_vars, sizeof(double));
      }
      else if (strcmp(key, "M") == 0){
         READ_INT_PAR(aux->num_lower_cons);
         aux->index_lower_cons = (int *) malloc (aux->num_lower_cons * sizeof(int));
      }
      else if (strcmp(key, "OS") == 0){
         READ_INT_PAR(aux->sense_lower_obj);
      }
      else if (strcmp(key, "LC") == 0){
         assert(var_count < aux->num_lower_vars);
         READ_INT_PAR(aux->index_lower_vars[var_count]);
         var_count++;
      }
      else if (strcmp(key, "LR") == 0){
         assert(cons_count < aux->num_lower_cons);
         READ_INT_PAR(aux->index_lower_cons[cons_count]);
         cons_count++;
      }
      else if (strcmp(key, "LO") == 0){
         assert(obj_coeff_count < aux->num_lower_vars);
         READ_DBL_PAR(aux->coeff_lower_obj[obj_coeff_count]);
         obj_coeff_count++;
      }
   }

   /* Fill out indicator arrays */
   aux->indicator_lower_vars  = (char*) calloc(prob->mip->n, CSIZE);
   aux->indicator_lower_cons  = (char*) calloc(prob->mip->m, CSIZE);
   for (i = 0; i < aux->num_lower_vars; i++) {
      aux->indicator_lower_vars[aux->index_lower_vars[i]] = 1;
   }
   for (i = 0; i < aux->num_lower_cons; i++) {
      aux->indicator_lower_cons[aux->index_lower_cons[i]] = 1;
   }

   if (f)
      fclose(f);

   return (FUNCTION_TERMINATED_NORMALLY);
}


/*===========================================================================*\
\*===========================================================================*/

int user_rearrange_mat_vec(user_problem *prob) {

   int n, m, nz, *column_starts, *temp_matrix_indices, *matrix_indices_col, *row_starts, *matrix_indices_row;
   int i, j, counter, counter2, *permutation_row, *permutation_col;
   int num_upper_vars, num_upper_cons;
   double *temp_matrix_values, *matrix_values_col, *matrix_values_row, *lb, *ub, *obj, *rhs, *rngval;
   char *is_int, *sense, **colname, **rowname, *indicator_lower_vars, *indicator_lower_cons;
   aux_data *aux = &(prob->aux);

   // Same number of variables, constraints, and number of nonzeros
   n = prob->mip->n;
   m = prob->mip->m;
   nz = prob->mip->matbeg[n];

   // number of upper level variables and constraints
   num_upper_vars = n - aux->num_lower_vars;
   num_upper_cons = m - aux->num_lower_cons;

   /* Allocate the arrays */
   column_starts              = (int *) malloc((n + 1) * ISIZE);
   matrix_indices_col         = (int *) malloc((nz) * ISIZE);
   matrix_values_col          = (double *) malloc((nz) * DSIZE);
   temp_matrix_indices        = (int *) malloc((nz) * ISIZE);
   temp_matrix_values         = (double *) malloc((nz) * DSIZE);
   row_starts                 = (int *) malloc((m + 1) * ISIZE);
   matrix_indices_row         = (int *) malloc((nz) * ISIZE);
   matrix_values_row          = (double *) malloc((nz) * DSIZE);
   obj                        = (double *) malloc(n * DSIZE);
   lb                         = (double *) malloc(n * DSIZE);
   ub                         = (double *) malloc(n * DSIZE);
   rhs                        = (double *) malloc(m * DSIZE);
   sense                      = (char *) malloc(m * CSIZE);
   rngval                     = (double *) calloc(m, DSIZE);
   is_int                     = (char *) malloc(n * CSIZE);
   permutation_col            = (int *) malloc(n * ISIZE);
   permutation_row            = (int *) malloc(m * ISIZE);
   indicator_lower_vars       = (char *) malloc(n * CSIZE);
   indicator_lower_cons       = (char *) malloc(m * CSIZE);

   /* Fill out rearranged arrays corresponding to variables */
   counter = 0;
   for (i = 0; i < n; i++) {
      if (!aux->indicator_lower_vars[i]) {
         lb[counter] = prob->mip->lb[i];
         ub[counter] = prob->mip->ub[i];
         obj[counter] = prob->mip->obj[i];
         is_int[counter] = prob->mip->is_int[i];
         counter++;
      }
   }
   for (i = 0; i < n; i++) {
      if (aux->indicator_lower_vars[i]) {
         lb[counter] = prob->mip->lb[i];
         ub[counter] = prob->mip->ub[i];
         obj[counter] = prob->mip->obj[i];
         is_int[counter] = prob->mip->is_int[i];
         counter++;
      }
   }

   /* Fill out rearranged arrays corresponding to constraints */
   counter = 0;
   for (i = 0; i < m; i++) {
      if (!aux->indicator_lower_cons[i]) {
         sense[counter] = prob->mip->sense[i];
         rngval[counter] = prob->mip->rngval[i];
         rhs[counter] = prob->mip->rhs[i];
         counter++;
      }
   }
   for (i = 0; i < m; i++) {
      if (aux->indicator_lower_cons[i]) {
         sense[counter] = prob->mip->sense[i];
         rngval[counter] = prob->mip->rngval[i];
         rhs[counter] = prob->mip->rhs[i];
         counter++;
      }
   }

   /* Permute variable indices w.r.t. rearrangement */
   counter = 0;
   for (i = 0; i < n; i++) {
      if (!aux->indicator_lower_vars[i]) {
         permutation_col[i] = counter;
         counter++;
      }
   }
   for (i = 0; i < n; i++) {
      if (aux->indicator_lower_vars[i]) {
         permutation_col[i] = counter;
         counter++;
      }
   }

   /* Permute constraint indices w.r.t. rearrangement */
   counter = 0;
   for (i = 0; i < m; i++) {
      if (!aux->indicator_lower_cons[i]) {
         permutation_row[i] = counter;
         counter++;
      }
   }
   for (i = 0; i < m; i++) {
      if (aux->indicator_lower_cons[i]) {
         permutation_row[i] = counter;
         counter++;
      }
   }

   /* Fill out column ordered arrays w.r.t. rearrangement */
   // Initially, create temporary arrays upon rearranging entire columns
   counter = 0;
   counter2 = 0;
   for (i = 0; i < n; i++) {
      if (!aux->indicator_lower_vars[i]) {
//         if (prob->mip->matbeg[i+1] - prob->mip->matbeg[i]) {
            column_starts[counter2] = counter;
            counter2++;
            for (j = prob->mip->matbeg[i]; j < prob->mip->matbeg[i+1]; j++) {
               temp_matrix_indices[counter] = prob->mip->matind[j];
               temp_matrix_values[counter] = prob->mip->matval[j];
               counter++;
            }
//         }
      }
   }
   for (i = 0; i < n; i++) {
      if (aux->indicator_lower_vars[i]) {
//         if (prob->mip->matbeg[i+1] - prob->mip->matbeg[i]) {
            column_starts[counter2] = counter;
            counter2++;
            for (j = prob->mip->matbeg[i]; j < prob->mip->matbeg[i+1]; j++) {
               temp_matrix_indices[counter] = prob->mip->matind[j];
               temp_matrix_values[counter] = prob->mip->matval[j];
               counter++;
            }
//         }
      }
   }
   column_starts[counter2] = counter;
   // Then, create actual column ordered arrays upon rearranging rows within each column
   counter = 0;
   counter2 = 0;
   for (i = 0; i < n; i++) {
//      if (column_starts[i+1] - column_starts[i]) {
         for (j = column_starts[i]; j < column_starts[i+1]; j++) {
            if (!aux->indicator_lower_cons[temp_matrix_indices[j]]) {
               matrix_indices_col[counter] = temp_matrix_indices[j];
               matrix_values_col[counter] = temp_matrix_values[j];
               counter++;
            }
         }
         for (j = column_starts[i]; j < column_starts[i+1]; j++) {
            if (aux->indicator_lower_cons[temp_matrix_indices[j]]) {
               matrix_indices_col[counter] = temp_matrix_indices[j];
               matrix_values_col[counter] = temp_matrix_values[j];
               counter++;
            }
         }
//      }
   }
   // Then, permute row indices to represent the new row numbers after rearrangement
   for (i = 0; i < nz; i++) {
      matrix_indices_col[i] = permutation_row[matrix_indices_col[i]];
   }

   /* Fill out row ordered arrays w.r.t. rearrangement */
   // Initially, create temporary arrays upon rearranging entire rows
   memset(temp_matrix_indices, 0, sizeof(temp_matrix_indices));
   memset(temp_matrix_values, 0, sizeof(temp_matrix_values));
   counter = 0;
   counter2 = 0;
   for (i = 0; i < m; i++) {
      if (!aux->indicator_lower_cons[i]) {
//         if (prob->matbeg_row[i+1] - prob->matbeg_row[i]) {
            row_starts[counter2] = counter;
            counter2++;
            for (j = prob->matbeg_row[i]; j < prob->matbeg_row[i+1]; j++) {
               temp_matrix_indices[counter] = prob->matind_row[j];
               temp_matrix_values[counter] = prob->matval_row[j];
               counter++;
            }
//         }
      }
   }
   for (i = 0; i < m; i++) {
      if (aux->indicator_lower_cons[i]) {
//         if (prob->matbeg_row[i+1] - prob->matbeg_row[i]) {
            row_starts[counter2] = counter;
            counter2++;
            for (j = prob->matbeg_row[i]; j < prob->matbeg_row[i+1]; j++) {
               temp_matrix_indices[counter] = prob->matind_row[j];
               temp_matrix_values[counter] = prob->matval_row[j];
               counter++;
            }
//         }
      }
   }
   row_starts[counter2] = counter;
   // Then, create actual row ordered arrays upon rearranging columns within each row 
   counter = 0;
   counter2 = 0;
   for (i = 0; i < m; i++) {
//      if (row_starts[i+1] - row_starts[i]) {
         for (j = row_starts[i]; j < row_starts[i+1]; j++) {
            if (!aux->indicator_lower_vars[temp_matrix_indices[j]]) {
               matrix_indices_row[counter] = temp_matrix_indices[j];
               matrix_values_row[counter] = temp_matrix_values[j];
               counter++;
            }
         }
         for (j = row_starts[i]; j < row_starts[i+1]; j++) {
            if (aux->indicator_lower_vars[temp_matrix_indices[j]]) {
               matrix_indices_row[counter] = temp_matrix_indices[j];
               matrix_values_row[counter] = temp_matrix_values[j];
               counter++;
            }
         }
//      }
   }
   // Then, permute column indices to represent the new column numbers after rearrangement
   for (i = 0; i < nz; i++) {
      matrix_indices_row[i] = permutation_col[matrix_indices_row[i]];
   }

   /* Rearrange indicator vectors */
   counter = 0;
   for (j = 0; j < n; j++) {
      if (!aux->indicator_lower_vars[j]) {
         indicator_lower_vars[counter] = 0;
         counter++;
      }
   }
   for (j = 0; j < n; j++) {
      if (aux->indicator_lower_vars[j]) {
         indicator_lower_vars[counter] = 1;
         counter++;
      }
   }
   counter = 0;
   for (j = 0; j < m; j++) {
      if (!aux->indicator_lower_cons[j]) {
         indicator_lower_cons[counter] = 0;
         counter++;
      }
   }
   for (j = 0; j < m; j++) {
      if (aux->indicator_lower_cons[j]) {
         indicator_lower_cons[counter] = 1;
         counter++;
      }
   }

   /* Rearrange column and row names */
   colname = (char **) malloc(sizeof(char *) * n);
   rowname = (char **) malloc(sizeof(char *) * m);

   counter = 0;
   for (j = 0; j < n; j++){
      if (!aux->indicator_lower_vars[j]) {
         colname[counter] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         strncpy(colname[counter], prob->mip->colname[j], MAX_NAME_SIZE);
         colname[counter][MAX_NAME_SIZE-1] = 0;
         counter++;
      }
   }
   for (j = 0; j < n; j++){
      if (aux->indicator_lower_vars[j]) {
         colname[counter] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         strncpy(colname[counter], prob->mip->colname[j], MAX_NAME_SIZE);
         colname[counter][MAX_NAME_SIZE-1] = 0;
         counter++;
      }
   }

   counter = 0;
   for (j = 0; j < m; j++){
      if (!aux->indicator_lower_cons[j]) {
         rowname[counter] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         strncpy(rowname[counter], prob->mip->rowname[j], MAX_NAME_SIZE);
         rowname[counter][MAX_NAME_SIZE-1] = 0;
         counter++;
      }
   }
   for (j = 0; j < m; j++){
      if (aux->indicator_lower_cons[j]) {
         rowname[counter] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         strncpy(rowname[counter], prob->mip->rowname[j], MAX_NAME_SIZE);
         rowname[counter][MAX_NAME_SIZE-1] = 0;
         counter++;
      }
   }

   /* Change original values to rearranged values */
   prob->mip->n = n;
   prob->mip->m = m;
   prob->mip->nz = nz;

   prob->mip->is_int  = (char *)   malloc(CSIZE * prob->mip->n);
   
   memcpy(prob->mip->obj, obj, DSIZE * prob->mip->n);
   memcpy(prob->mip->rhs, rhs, DSIZE * prob->mip->m);
   memcpy(prob->mip->sense, sense, CSIZE * prob->mip->m);
   memcpy(prob->mip->rngval, rngval, DSIZE * prob->mip->m);
   memcpy(prob->mip->ub, ub, DSIZE * prob->mip->n);
   memcpy(prob->mip->lb, lb, DSIZE * prob->mip->n);
   memcpy(prob->mip->is_int, is_int, CSIZE * prob->mip->n);
   for (j = 0; j < n; j++){
      prob->mip->colname[j] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(prob->mip->colname[j], colname[j], MAX_NAME_SIZE);
      prob->mip->colname[j][MAX_NAME_SIZE-1] = 0;
   }
   for (j = 0; j < m; j++){
      prob->mip->rowname[j] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(prob->mip->rowname[j], rowname[j], MAX_NAME_SIZE);
      prob->mip->rowname[j][MAX_NAME_SIZE-1] = 0;
   }

   memcpy(prob->mip->matbeg, column_starts, ISIZE * (prob->mip->n + 1));
   memcpy(prob->mip->matval, matrix_values_col, DSIZE * prob->mip->matbeg[prob->mip->n]);
   memcpy(prob->mip->matind, matrix_indices_col, ISIZE * prob->mip->matbeg[prob->mip->n]);

   memcpy(prob->matbeg_row, row_starts, ISIZE * (prob->mip->m + 1));
   memcpy(prob->matval_row, matrix_values_row, DSIZE * prob->matbeg_row[prob->mip->m]);
   memcpy(prob->matind_row, matrix_indices_row, ISIZE * prob->matbeg_row[prob->mip->m]);

   // Change lower level variables and constraint indices in auxiliary info structure
   for (j = num_upper_vars; j < prob->mip->n; j++) {
      aux->index_lower_vars[j - num_upper_vars] = j;
   }
   for (j = num_upper_cons; j < prob->mip->m; j++) {
      aux->index_lower_cons[j - num_upper_cons] = j;
   }

   // Finally, replace indicator arrays too
   memcpy(aux->indicator_lower_vars, indicator_lower_vars, CSIZE * prob->mip->n);
   memcpy(aux->indicator_lower_cons, indicator_lower_cons, CSIZE * prob->mip->m);

   FREE(column_starts);
   FREE(matrix_indices_col);
   FREE(matrix_values_col);
   FREE(row_starts);
   FREE(matrix_indices_row);
   FREE(matrix_values_row);
   FREE(temp_matrix_indices);
   FREE(temp_matrix_values);
   FREE(permutation_col);
   FREE(permutation_row);
   FREE(lb);
   FREE(ub);
   FREE(obj);
   FREE(sense);
   FREE(rhs);
   FREE(rngval);
   FREE(is_int);
   FREE(colname);
   FREE(rowname);
   FREE(indicator_lower_vars);
   FREE(indicator_lower_cons);

   return (FUNCTION_TERMINATED_NORMALLY);
}


/*===========================================================================*\
   For various preprocessing operations on orig. prob. as single-level prob.:
   (1) Variable bound tightening of original cols
   (2)
\*===========================================================================*/

int user_preprocess_single_level_prob(user_problem *prob) {

    /* Variable bound tightening */
    user_orig_col_bound_tightening(prob);

}


/*===========================================================================*\
       Variable bound tightening of original cols
\*===========================================================================*/

int user_orig_col_bound_tightening(user_problem *prob) {

   //SYMPHONY environment
   sym_environment *env = sym_open_environment();

   /* Load continuous version of the given instance to SYMPHONY */
   sym_explicit_load_problem(env, prob->mip->n, prob->mip->m, prob->mip->matbeg,
			     prob->mip->matind, prob->mip->matval,
                             prob->mip->lb, prob->mip->ub, NULL, prob->mip->obj,
                             NULL, prob->mip->sense, prob->mip->rhs,
			     prob->mip->rngval, true);

   //Get certain data for the given instance
   warm_start_desc * ws;
   int num_cols, num_rows, i;
   double *orig_lb, *orig_ub, new_lb, new_ub, etol = 1e-6;

   num_cols = prob->mip->n;
   num_rows = prob->mip->m;
   orig_lb = prob->mip->lb;
   orig_ub = prob->mip->ub;

   //Set parameters for warm starting
   sym_set_int_param(env, "keep_warm_start", TRUE);
   sym_set_int_param(env, "do_reduced_cost_fixing", 0);
   sym_set_int_param(env, "do_primal_heuristic", 0);
   sym_set_int_param(env, "prep_level", -1);
   sym_set_int_param(env, "verbosity", -5);

   /* Solve a minimization problem corresponding to first variable,
    * i.e., minimize first variable s.t. given two levels of constraints.
   */
   //Set objective function at first
   sym_set_obj_coeff(env, 0, 1);
   for (i = 1; i < num_cols; i++) {
       sym_set_obj_coeff(env, i, 0);
   }
   sym_set_obj_sense(env, 1);
   //Now, solve the problem and get useful information
   sym_solve(env);
   sym_get_obj_val(env, &new_lb);
   ws = sym_get_warm_start(env, true);

   //Certain parameters
   int total_bound_changes = 0, threshold_bound_changes = int(0.25*2*num_cols);
   int total_refinements = 4, j;

   //Reset certain (unwanted) parameters to defaults
   sym_set_int_param(env, "keep_warm_start", FALSE);
   sym_set_int_param(env, "do_reduced_cost_fixing", 1);
   sym_set_int_param(env, "do_primal_heuristic", 1);
//   sym_set_int_param(env, "prep_level", 5);

   for (j = 0; j < total_refinements; j++) {
      /* Solve remaining minimization problems for other variables */
      for (i = 1; i < num_cols; i++) {
         //Changing LB of previous variable if better bound found
         if (new_lb >= orig_lb[i-1] + etol) {
            sym_set_col_lower(env, i-1, new_lb);
            orig_lb[i-1] = new_lb;
            total_bound_changes++;
         }
         //Changing objective function relative to previous objective function
         sym_set_obj_coeff(env, i-1, 0);
         sym_set_obj_coeff(env, i, 1);
         //Now, solve the problem and get useful information
         sym_set_warm_start(env, ws);

         sym_warm_solve(env);
         sym_get_obj_val(env, &new_lb);
      }
      //Changing LB of last variable if better bound found
      if (new_lb >= orig_lb[i-1] + etol) {
         sym_set_col_lower(env, i-1, new_lb);
         orig_lb[i-1] = new_lb;
         total_bound_changes++;
      }

      /* Now, solve the maximization problem for first variable */
      //Changing objective function relative to previous objective function
      sym_set_obj_coeff(env, num_cols-1, 0);
      sym_set_obj_coeff(env, 0, -1);
      //Now, solve the problem and get useful information
      sym_set_warm_start(env, ws);

      sym_warm_solve(env);
      sym_get_obj_val(env, &new_ub);

      /* Solve remaining maximization problems for other variables */
      for (i = 1; i < num_cols; i++) {
         //Changing UB of previous variable if better bound found
         if (-new_ub <= orig_ub[i-1] - etol) {
            sym_set_col_upper(env, i-1, -new_ub);
            orig_ub[i-1] = -new_ub;
            total_bound_changes++;
         }
         //Changing objective function relative to previous objective function
         sym_set_obj_coeff(env, i-1, 0);
         sym_set_obj_coeff(env, i, -1);
         //Now, solve the problem and get useful information
         sym_set_warm_start(env, ws);

         sym_warm_solve(env);
         sym_get_obj_val(env, &new_ub);
      }
      //Changing UB of last variable if better bound found
      if (-new_ub <= orig_ub[i-1] - etol) {
         sym_set_col_upper(env, i-1, -new_ub);
         orig_ub[i-1] = -new_ub;
         total_bound_changes++;
      }
      printf("\nMAIN: Done solving all min/max bounding problems in refinement %d\n\n", j);

      if (total_bound_changes >= threshold_bound_changes) {
         //Reset total_bound_changes
         total_bound_changes = 0;

         //Changing objective function back to minimizing first coefficient
         sym_set_obj_coeff(env, i-1, 0);
         sym_set_obj_coeff(env, 0, 1);
         //Now, solve the problem and get useful information
         sym_set_warm_start(env, ws);

         sym_warm_solve(env);
         sym_get_obj_val(env, &new_lb);
      } else {
         break;
      }
   }

   FREE(ws);
   sym_close_environment(env);
}


/*===========================================================================*\
 * TODO: Suresh: 
 *        Assumptions in bilevel benchmarks:
 *         1. All upper level variables occur before any lower level variables.
 *         2. All upper level constraints occur before any lower level constraint.
\*===========================================================================*/

int user_generate_bilevel_problem(sym_environment *env, user_problem *prob) {

   int i, j, index, index1, n, m, nz, nz_index = 0, *column_starts, *matrix_indices;
   double *matrix_values, *lb, *ub, *obj, *rhs, *rngval;
   char *sense, *is_int, obj_sense = 1.0; // TODO: obj_sense = 1.0 always?
   aux_data *aux = &(prob->aux);

   /* Find some info about bounds */
   prob->ubinfty = 0;
   prob->lbinfty = 0;
   prob->infubind     = (int *) calloc(prob->mip->n, ISIZE);
   prob->inflbind     = (int *) calloc(prob->mip->n, ISIZE);
   prob->infubsofar   = (int *) malloc(ISIZE * prob->mip->n);
   prob->inflbsofar   = (int *) malloc(ISIZE * prob->mip->n);
   // count number of infinity UBs and -infinity LBs, and also their indicators.
   for (j = 0; j < prob->mip->n; j++) {
      prob->infubsofar[j] = prob->ubinfty;
      if (prob->mip->ub[j] >= prob->infty) {
         prob->ubinfty++;
         prob->infubind[j] = 1;
      }
      prob->inflbsofar[j] = prob->lbinfty;
      if (prob->mip->lb[j] <= -prob->infty) {
         prob->lbinfty++;
         prob->inflbind[j] = 1;
      }
   }

   /****************************************************************************\
    * Consider the coefficient matrix (of both upper and lower level primal cons)
    * division as shown below.
    * nz_1 = # of nonzeros in upper level cons corresponding to upper level vars.
    * nz_2 = # of nonzeros in upper level cons corresponding to lower level vars.
    * nz_3 = # of nonzeros in lower level cons corresponding to upper level vars.
    * nz_4 = # of nonzeros in lower level cons corresponding to lower level vars.
    *          -------------
    *          | nz_1|nz_2 |
    *          |-----------|
    *          | nz_3|nz_4 |
    *          -------------
   \****************************************************************************/

   // number of upper level variables
   int num_upperlevel_vars = prob->mip->n - aux->num_lower_vars;
   // number of upper level constraints
   int num_upperlevel_cons = prob->mip->m - aux->num_lower_cons;
   // nz_1 as described above
   int nz_1 = 0;

   for (i = 0; i < num_upperlevel_vars; i++) {
      if ((prob->mip->matbeg[i+1] - prob->mip->matbeg[i]) > 0) {
         for (j = prob->mip->matbeg[i]; j < prob->mip->matbeg[i+1]; j++) {
            if (prob->mip->matind[j] < num_upperlevel_cons) {
               nz_1++;
            }
         }
      }
   }

   // TODO: Suresh: following two names are misleading. Fix them later.
   // number of nonzeros in lower level constraint coeffs corresponding to upper level variables
   int nz_upperlevel = prob->mip->matbeg[num_upperlevel_vars] - nz_1;
   // number of nonzeros in lower level constraint coeffs corresponding to lower level variables
   int nz_lowerlevel = prob->mip->matbeg[prob->mip->n] - prob->matbeg_row[num_upperlevel_cons] - nz_upperlevel;
   // number of lower level finite upper bound constraints on variables
   int num_lowerlevel_ubcons = (prob->mip->n - num_upperlevel_vars - (prob->ubinfty - prob->infubsofar[num_upperlevel_vars]));
   // number of lower level dual variables on finite upper bound constraints
   int num_lowerlevel_dual_ubvars = num_lowerlevel_ubcons;
   // number of lower level finite lower bound constrains on variables
   int num_lowerlevel_lbcons = (prob->mip->n - num_upperlevel_vars - (prob->lbinfty - prob->inflbsofar[num_upperlevel_vars]));
   // number of lower level dual variables on finite lower bound constraints
   int num_lowerlevel_dual_lbvars = num_lowerlevel_lbcons;
   // number of nonzeros per row in lower level part of coefficient matrix
   int *nz_lowerlevel_row;

   /* set up the inital LP data */
   n = prob->mip->n + (prob->mip->m - num_upperlevel_cons) + num_lowerlevel_dual_ubvars + num_lowerlevel_dual_lbvars;
   m = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + (prob->mip->n - num_upperlevel_vars);
   nz = prob->mip->matbeg[prob->mip->n] + 2*num_lowerlevel_ubcons + 2*num_lowerlevel_lbcons + nz_lowerlevel;
   prob->colnum = n;
   prob->rownum = m;

   /* Allocate the arrays */
   column_starts  = (int *) malloc((n + 1) * ISIZE);
   matrix_indices = (int *) malloc((nz) * ISIZE);
   matrix_values  = (double *) malloc((nz) * DSIZE);
   obj            = (double *) malloc(n * DSIZE);
   lb             = (double *) malloc(n * DSIZE);
   ub             = (double *) malloc(n * DSIZE);
   rhs            = (double *) malloc(m * DSIZE);
   sense          = (char *) malloc(m * CSIZE);
   rngval         = (double *) calloc(m, DSIZE); /* TODO:Correct the assumption that this is zero always */
   is_int         = (char *) malloc(n * CSIZE);
   
   /* Fill out the appropriate data structures */
   if (prob->mip->obj_sense > 0.0) {
      for (i = 0; i < n; i++) {
         if (i < prob->mip->n) {
            obj[i] = prob->mip->obj[i];
         } else {
            obj[i] = 0.0;
         }
      }
   } else {
      for (i = 0; i < n; i++) {
         if (i < prob->mip->n) {
            obj[i] = -prob->mip->obj[i];
         } else {
            obj[i] = 0.0;
         }
      }
   }
   env->mip->colname = (char **) malloc(sizeof(char *) * n);  
   env->mip->rowname = (char **) malloc(sizeof(char *) * m);  

   /* The original upper level variables */
   for (i = 0; i < num_upperlevel_vars; i++) {
      is_int[i] = FALSE;
      ub[i] = prob->mip->ub[i];
      lb[i] = prob->mip->lb[i];
      env->mip->colname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(env->mip->colname[i], prob->mip->colname[i], MAX_NAME_SIZE);
      env->mip->colname[i][MAX_NAME_SIZE-1] = 0;
   }
   /* The original lower level variables */
   for (; i < prob->mip->n; i++) {
      is_int[i] = FALSE;
      ub[i] = prob->infty;
      lb[i] = -prob->infty;
      env->mip->colname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(env->mip->colname[i], prob->mip->colname[i], MAX_NAME_SIZE);
      env->mip->colname[i][MAX_NAME_SIZE-1] = 0;
   }
   /* The duals on original lower level constraints */
   if (aux->sense_lower_obj > 0) {
      for (;i < prob->mip->n + prob->mip->m - num_upperlevel_cons; i++) {
         is_int[i] = FALSE;
         if (prob->mip->sense[i - prob->mip->n + num_upperlevel_cons] == 'L') {
            ub[i] = 0;
            lb[i] = -prob->infty;
         } else if (prob->mip->sense[i - prob->mip->n + num_upperlevel_cons] == 'G') {
            ub[i] = prob->infty;
            lb[i] = 0;
         } else {
            ub[i] = prob->infty;
            lb[i] = -prob->infty;
         }
         env->mip->colname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         env->mip->colname[i][0] = 'D';
         env->mip->colname[i][1] = '_';
         strncpy(env->mip->colname[i]+2, prob->mip->rowname[i - prob->mip->n + num_upperlevel_cons],
               MAX_NAME_SIZE-2);
         env->mip->colname[i][MAX_NAME_SIZE-1] = 0;
      }
   } else {
      for (;i < prob->mip->n + prob->mip->m - num_upperlevel_cons; i++) {
         is_int[i] = FALSE;
         if (prob->mip->sense[i - prob->mip->n + num_upperlevel_cons] == 'L') {
            ub[i] = prob->infty;
            lb[i] = 0;
         } else if (prob->mip->sense[i - prob->mip->n + num_upperlevel_cons] == 'G') {
            ub[i] = 0;
            lb[i] = -prob->infty;
         } else {
            ub[i] = prob->infty;
            lb[i] = -prob->infty;
         }
         env->mip->colname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         env->mip->colname[i][0] = 'D';
         env->mip->colname[i][1] = '_';
         strncpy(env->mip->colname[i]+2, prob->mip->rowname[i - prob->mip->n + num_upperlevel_cons],
               MAX_NAME_SIZE-2);
         env->mip->colname[i][MAX_NAME_SIZE-1] = 0;
      }
   }

   /* The duals on lower level variable upper bound constraints */
   if (aux->sense_lower_obj > 0) {
      for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
         if (prob->mip->ub[j] >= prob->infty) {
            continue;
         }
         index = prob->mip->n + (prob->mip->m - num_upperlevel_cons) + ((j - num_upperlevel_vars) - (prob->infubsofar[j] - prob->infubsofar[num_upperlevel_vars]));
         is_int[index] = FALSE;
         ub[index] = 0.0;
         lb[index] = -prob->infty;
         env->mip->colname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         env->mip->colname[index][0] = 'U';
         env->mip->colname[index][1] = '_';
         strncpy(env->mip->colname[index]+2, prob->mip->colname[j],
               MAX_NAME_SIZE-2);
         env->mip->colname[index][MAX_NAME_SIZE-1] = 0;
         i++;
      }
   } else {
      for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
         if (prob->mip->ub[j] >= prob->infty) {
            continue;
         }
         index = prob->mip->n + (prob->mip->m - num_upperlevel_cons) + ((j - num_upperlevel_vars) - (prob->infubsofar[j] - prob->infubsofar[num_upperlevel_vars]));
         is_int[index] = FALSE;
         ub[index] = prob->infty;
         lb[index] = 0.0;
         env->mip->colname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         env->mip->colname[index][0] = 'U';
         env->mip->colname[index][1] = '_';
         strncpy(env->mip->colname[index]+2, prob->mip->colname[j],
               MAX_NAME_SIZE-2);
         env->mip->colname[index][MAX_NAME_SIZE-1] = 0;
         i++;
      }
   }

   /* The duals on lower level variable lower bound constraints */
   if (aux->sense_lower_obj > 0) {
      for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
         if (prob->mip->lb[j] <= -prob->infty) {
            continue;
         }
         index = prob->mip->n + (prob->mip->m - num_upperlevel_cons) + num_lowerlevel_dual_ubvars + ((j - num_upperlevel_vars) - (prob->inflbsofar[j] - prob->inflbsofar[num_upperlevel_vars]));
         is_int[index] = FALSE;
         ub[index] = prob->infty;
         lb[index] = 0.0;
         env->mip->colname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         env->mip->colname[index][0] = 'L';
         env->mip->colname[index][1] = '_';
         strncpy(env->mip->colname[index]+2, prob->mip->colname[j],
               MAX_NAME_SIZE-2);
         env->mip->colname[index][MAX_NAME_SIZE-1] = 0;
         i++;
      }
   } else {
      for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
         if (prob->mip->lb[j] <= -prob->infty) {
            continue;
         }
         index = prob->mip->n + (prob->mip->m - num_upperlevel_cons) + num_lowerlevel_dual_ubvars + ((j - num_upperlevel_vars) - (prob->inflbsofar[j] - prob->inflbsofar[num_upperlevel_vars]));
         is_int[index] = FALSE;
         ub[index] = 0.0;
         lb[index] = -prob->infty;
         env->mip->colname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
         env->mip->colname[index][0] = 'L';
         env->mip->colname[index][1] = '_';
         strncpy(env->mip->colname[index]+2, prob->mip->colname[j],
               MAX_NAME_SIZE-2);
         env->mip->colname[index][MAX_NAME_SIZE-1] = 0;
         i++;
      }
   }

   /* The original upper level and lower level constraints */
   for (i = 0; i < prob->mip->m; i++) {
      sense[i] = prob->mip->sense[i];
      rhs[i] = prob->mip->rhs[i];
      env->mip->rowname[i] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      strncpy(env->mip->rowname[i], prob->mip->rowname[i], MAX_NAME_SIZE);
      env->mip->rowname[i][MAX_NAME_SIZE-1] = 0;
   }
   /* The lower level upper bound constraints on variables */
   for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
      if (prob->mip->ub[j] >= prob->infty) {
         continue;
      }
      index = prob->mip->m + ((j - num_upperlevel_vars) - (prob->infubsofar[j] - prob->infubsofar[num_upperlevel_vars]));
      sense[index] = 'L';
      rhs[index] = prob->mip->ub[j];
      env->mip->rowname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->rowname[index][0] = 'U';
      env->mip->rowname[index][1] = '_';
      strncpy(env->mip->rowname[index]+2, prob->mip->colname[j],
            MAX_NAME_SIZE-2);
      env->mip->rowname[index][MAX_NAME_SIZE-1] = 0;
      i++;
   }

   /* The lower level lower bound constraints on variables */
   for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
      if (prob->mip->lb[j] <= -prob->infty) {
         continue;
      }
      index = prob->mip->m + num_lowerlevel_ubcons + ((j - num_upperlevel_vars) - (prob->inflbsofar[j] - prob->inflbsofar[num_upperlevel_vars]));
      sense[index] = 'G';
      rhs[index] = prob->mip->lb[j];
      env->mip->rowname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->rowname[index][0] = 'L';
      env->mip->rowname[index][1] = '_';
      strncpy(env->mip->rowname[index]+2, prob->mip->colname[j],
            MAX_NAME_SIZE-2);
      env->mip->rowname[index][MAX_NAME_SIZE-1] = 0;
      i++;
   }

   /* The lower level dual constraints */
   for (j = num_upperlevel_vars; j < prob->mip->n; j++) {
      index = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + ((j - num_upperlevel_vars));
      sense[index] = 'E';
      // Suresh: this rhs is lower level obj coeff
      rhs[index] = aux->coeff_lower_obj[j - num_upperlevel_vars];
      env->mip->rowname[index] = (char *) malloc(CSIZE * MAX_NAME_SIZE);
      env->mip->rowname[index][0] = 'E';
      env->mip->rowname[index][1] = '_';
      strncpy(env->mip->rowname[index]+2, prob->mip->colname[j],
	      MAX_NAME_SIZE-2);
      env->mip->rowname[index][MAX_NAME_SIZE-1] = 0;
      i++;
   }

   /* column sparse format entries corresponding to original upper level variables */
   column_starts[0] = 0;
   for (i = 0; i < num_upperlevel_vars; i++) {
      column_starts[i+1] = column_starts[i] + prob->mip->matbeg[i+1] - prob->mip->matbeg[i];
      if (prob->mip->matbeg[i + 1] - prob->mip->matbeg[i] > 0) {
         for (j = (prob->mip->matbeg[i]); j < (prob->mip->matbeg[i + 1]); j++) {
            matrix_values[nz_index] = prob->mip->matval[j];
            matrix_indices[nz_index] = prob->mip->matind[j];
            nz_index++;
         }
      }
   }

   /* column sparse format entries corresponding to original lower level variables */
   for (; i < prob->mip->n; i++) {
      column_starts[i+1] = column_starts[i] + prob->mip->matbeg[i+1] - prob->mip->matbeg[i] + 2 - prob->infubind[i] - prob->inflbind[i];
      if (prob->mip->matbeg[i + 1] - prob->mip->matbeg[i] > 0) {
         for (j = (prob->mip->matbeg[i]); j < (prob->mip->matbeg[i + 1]); j++) {
            matrix_values[nz_index] = prob->mip->matval[j];
            matrix_indices[nz_index] = prob->mip->matind[j];
            nz_index++;
         }
      }
      if (!prob->infubind[i]) {
         matrix_values[nz_index] = 1.0;
         matrix_indices[nz_index] = prob->mip->m + ((i - num_upperlevel_vars) - (prob->infubsofar[i] - prob->infubsofar[num_upperlevel_vars]));
         nz_index++;
      }
      if (!prob->inflbind[i]) {
         matrix_values[nz_index] = 1.0;
         matrix_indices[nz_index] = prob->mip->m + num_lowerlevel_ubcons + ((i - num_upperlevel_vars) - (prob->inflbsofar[i] - prob->inflbsofar[num_upperlevel_vars]));
         nz_index++;
      }
   }

   /* column sparse format entries corresponding to dual variables on original lower level constraints */
   // At first, find number of nonzeros per row in the lower level coefficient part of matrix
   nz_lowerlevel_row = (int *) malloc((prob->mip->m - num_upperlevel_cons) * ISIZE);
   for (i = num_upperlevel_cons; i < prob->mip->m; i++) {
      nz_lowerlevel_row[i - num_upperlevel_cons] = prob->matbeg_row[i+1] - prob->matbeg_row[i];
      if ((prob->matbeg_row[i+1] - prob->matbeg_row[i]) > 0) {
         for (j = prob->matbeg_row[i]; j < prob->matbeg_row[i+1]; j++) {
            if (prob->matind_row[j] < num_upperlevel_vars) {
               nz_lowerlevel_row[i - num_upperlevel_cons]--;
            }
         }
      }
   }
   // Now update column sparse format entries as required
   index = 0;
   for (i = num_upperlevel_cons; i < prob->mip->m; i++) {
      column_starts[prob->mip->n + 1 + index] = column_starts[prob->mip->n + index] + nz_lowerlevel_row[i - num_upperlevel_cons];
      index++;
      for (j = prob->matbeg_row[i]; j < prob->matbeg_row[i+1]; j++) {
         if (prob->matind_row[j] >= num_upperlevel_vars) {
            matrix_values[nz_index] = prob->matval_row[j];
            matrix_indices[nz_index] = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + (prob->matind_row[j] - num_upperlevel_vars);
            nz_index++;
         }
      }
   }

   /* column sparse format entries corresponding to dual variables on lower level primal UB constraints */
   for (i = num_upperlevel_vars; i < prob->mip->n; i++) {
      if (!prob->infubind[i]) {
         column_starts[prob->mip->n + 1 + index] = column_starts[prob->mip->n + index] + 1;
         index++;
         matrix_values[nz_index] = 1.0;
         matrix_indices[nz_index] = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + (i - num_upperlevel_vars);
         nz_index++;
      }
   }
   /* column sparse format entries corresponding to dual variables on lower level primal LB constraints */
   for (i = num_upperlevel_vars; i < prob->mip->n; i++) {
      if (!prob->inflbind[i]) {
         column_starts[prob->mip->n + 1 + index] = column_starts[prob->mip->n + index] + 1;
         index++;
         matrix_values[nz_index] = 1.0;
         matrix_indices[nz_index] = prob->mip->m + num_lowerlevel_ubcons + num_lowerlevel_lbcons + (i - num_upperlevel_vars);
         nz_index++;
      }
   }

   /* Assign memory and fill complementarity constraint indices for variables */
   prob->ccind          =   (int *) malloc(n * ISIZE);
   prob->ccnum          =   0;
   index = 0;
   index1 = num_upperlevel_cons;
   for (i = 0; i < n; i++) {
      if (i < prob->mip->n) {
         prob->ccind[i] = -1;
      } else if (i < prob->mip->n + prob->mip->m - num_upperlevel_cons) {
         if (sense[i - prob->mip->n + num_upperlevel_cons] == 'E') {
            prob->ccind[i] = -1;
            index1++;
         } else {
            prob->ccind[i] = index1;
            prob->ccnum++;
            index1++;
         }
      } else {
         prob->ccind[i] = index1;
         prob->ccnum++;
         index1++;
      }
   }

   /* Load the problem to SYMPHONY */   
   /*
   sym_explicit_load_problem(env, n, m, column_starts, matrix_indices,
			     matrix_values, lb, ub, is_int, obj, 0, sense, rhs,
			     rngval, true);
   */

   /* Change prob->mip values to final problem values */
   prob->mip->n = n;
   prob->mip->m = m;
   prob->mip->nz = nz;
   prob->mip->obj_sense = obj_sense;

   prob->mip->obj    = (double *) realloc(prob->mip->obj, DSIZE * prob->mip->n);
   prob->mip->rhs    = (double *) realloc(prob->mip->rhs, DSIZE * prob->mip->m);
   prob->mip->sense  = (char *)   realloc(prob->mip->sense, CSIZE * prob->mip->m);
   prob->mip->rngval = (double *) realloc(prob->mip->rngval, DSIZE * prob->mip->m);
   prob->mip->ub     = (double *) realloc(prob->mip->ub, DSIZE * prob->mip->n);
   prob->mip->lb     = (double *) realloc(prob->mip->lb, DSIZE * prob->mip->n);
   prob->mip->is_int = (char *)   malloc(CSIZE * prob->mip->n);
   /* Default values for vvind, vvnum, feasible and rowact */
//   prob->mip->feasible    = USER__DO_NOT_BRANCH;
//   prob->mip->vvind       = (int *)    calloc(prob->mip->n, ISIZE);
//   prob->mip->vvnum       = 0;
//   prob->mip->rowact      = (double *) calloc(prob->mip->m, DSIZE);
   
   memcpy(prob->mip->obj, obj, DSIZE * prob->mip->n);
   memcpy(prob->mip->rhs, rhs, DSIZE * prob->mip->m);
   memcpy(prob->mip->sense, sense, CSIZE * prob->mip->m);
//   memset(prob->mip->rngval, 0, DSIZE * m);
   memset(prob->mip->rngval, 0, sizeof(prob->mip->rngval));                     // TODO: Fix this assumption.
   memcpy(prob->mip->ub, ub, DSIZE * prob->mip->n);
   memcpy(prob->mip->lb, lb, DSIZE * prob->mip->n);
   memcpy(prob->mip->is_int, is_int, CSIZE * prob->mip->n);

   prob->mip->matbeg = (int *) realloc(prob->mip->matbeg, ISIZE * (prob->mip->n + 1));
   memcpy(prob->mip->matbeg, column_starts, ISIZE * (prob->mip->n + 1));
   
   prob->mip->matval = (double *) realloc(prob->mip->matval, DSIZE*prob->mip->matbeg[prob->mip->n]);
   prob->mip->matind = (int *)    realloc(prob->mip->matind, ISIZE*prob->mip->matbeg[prob->mip->n]);
   
   memcpy(prob->mip->matval, matrix_values, DSIZE * prob->mip->matbeg[prob->mip->n]);
   memcpy(prob->mip->matind, matrix_indices, ISIZE * prob->mip->matbeg[prob->mip->n]);

   /* TODO: Delete mat*_row vectors here? */
   FREE(column_starts);
   FREE(matrix_indices);
   FREE(matrix_values);
   FREE(lb);
   FREE(ub);
   FREE(obj);
   FREE(sense);
   FREE(rhs);
   FREE(rngval);
   FREE(is_int);
   FREE(nz_lowerlevel_row);
   /* TODO: Is it good to free infubind, inflbind, ifubsofar, inflbsofar here? */
   FREE(prob->inflbsofar);
   FREE(prob->infubsofar);
   FREE(prob->inflbind);
   FREE(prob->infubind);
   FREE(prob->matval_row);
   FREE(prob->matind_row);
   FREE(prob->matbeg_row);

   return (FUNCTION_TERMINATED_NORMALLY);
}


/*===========================================================================*\
   For various preprocessing operations on the bilevel prob.:
   (1) Variable bound tightening
   (2)
\*===========================================================================*/

int user_preprocess_bilevel_prob(user_problem *prob) {

    /* Variable bound tightening */
    user_col_bound_tightening(prob);

}


/*===========================================================================*\
       Variable bound tightening
\*===========================================================================*/

int user_col_bound_tightening(user_problem *prob) {

   //SYMPHONY environment
   sym_environment *env = sym_open_environment();

   /* Load continuous version of the given instance to SYMPHONY */
   sym_explicit_load_problem(env, prob->mip->n, prob->mip->m, prob->mip->matbeg,
			     prob->mip->matind, prob->mip->matval,
                             prob->mip->lb, prob->mip->ub, NULL, prob->mip->obj,
                             NULL, prob->mip->sense, prob->mip->rhs,
			     prob->mip->rngval, true);

   //Get certain data for the given instance
   warm_start_desc * ws;
   int num_cols, num_rows, i, *ccind;
   double *orig_lb, *orig_ub, new_lb, new_ub, etol = 1e-6;
   char *sense;

   num_cols = prob->mip->n;
   num_rows = prob->mip->m;
   ccind = prob->ccind;
   orig_lb = prob->mip->lb;
   orig_ub = prob->mip->ub;
   sense = prob->mip->sense;

   //Set parameters for warm starting
   sym_set_int_param(env, "keep_warm_start", TRUE);
   sym_set_int_param(env, "do_reduced_cost_fixing", 0);
   sym_set_int_param(env, "do_primal_heuristic", 0);
   sym_set_int_param(env, "prep_level", -1);
   sym_set_int_param(env, "verbosity", -5);

   /* Solve a minimization problem corresponding to first variable,
    * i.e., minimize first variable s.t. all linear constraints.
   */
   //Set objective function at first
   sym_set_obj_coeff(env, 0, 1);
   for (i = 1; i < num_cols; i++) {
       sym_set_obj_coeff(env, i, 0);
   }
   sym_set_obj_sense(env, 1);
   //Now, solve the problem and get useful information
   sym_solve(env);
   sym_get_obj_val(env, &new_lb);
   ws = sym_get_warm_start(env, true);

   //Certain parameters
   int total_bound_changes = 0, threshold_bound_changes = int(0.25*2*num_cols);
   int total_refinements = 4, j, ccindex;

   //Reset certain (unwanted) parameters to defaults
   sym_set_int_param(env, "keep_warm_start", FALSE);
   sym_set_int_param(env, "do_reduced_cost_fixing", 1);
   sym_set_int_param(env, "do_primal_heuristic", 1);
//   sym_set_int_param(env, "prep_level", 5);

   for (j = 0; j < total_refinements; j++) {
      /* Solve remaining minimization problems for other variables */
      for (i = 1; i < num_cols; i++) {
         //If better bound found:
         if (new_lb >= orig_lb[i-1] + etol) {
            //Changing LB of appropriate col.
            sym_set_col_lower(env, i-1, new_lb);
            orig_lb[i-1] = new_lb;

            //Incrementing total_bound_changes
            total_bound_changes++;

            //Checking if new_lb > 0
            if (new_lb >= etol) {
               //Make certain changes if a complementarity condition exists
               ccindex = ccind[i-1];
               if (ccindex >= 0) {
                  sense[ccindex] = 'E';
                  ccind[i-1] = -1;
               }
            }
         }
         //Changing objective function relative to previous objective function
         sym_set_obj_coeff(env, i-1, 0);
         sym_set_obj_coeff(env, i, 1);
         //Now, solve the problem and get useful information
         sym_set_warm_start(env, ws);

         sym_warm_solve(env);
         sym_get_obj_val(env, &new_lb);
      }
      //If better bound for last column found:
      if (new_lb >= orig_lb[i-1] + etol) {
         //Changing LB of appropriate col.
         sym_set_col_lower(env, i-1, new_lb);
         orig_lb[i-1] = new_lb;

         //Incrementing total_bound_changes
         total_bound_changes++;

         //Checking if new_lb > 0
         if (new_lb >= etol) {
            //Make certain changes if a complementarity condition exists
            ccindex = ccind[i-1];
            if (ccindex >= 0) {
               sense[ccindex] = 'E';
               ccind[i-1] = -1;
            }
         }
      }

      /* Now, solve the maximization problem for first variable */
      //Changing objective function relative to previous objective function
      sym_set_obj_coeff(env, num_cols-1, 0);
      sym_set_obj_coeff(env, 0, -1);
      //Now, solve the problem and get useful information
      sym_set_warm_start(env, ws);

      sym_warm_solve(env);
      sym_get_obj_val(env, &new_ub);

      /* Solve remaining maximization problems for other variables */
      for (i = 1; i < num_cols; i++) {
         //Changing UB of previous variable if better bound found
         if (-new_ub <= orig_ub[i-1] - etol) {
            sym_set_col_upper(env, i-1, -new_ub);
            orig_ub[i-1] = -new_ub;
            total_bound_changes++;
         }
         //Changing objective function relative to previous objective function
         sym_set_obj_coeff(env, i-1, 0);
         sym_set_obj_coeff(env, i, -1);
         //Now, solve the problem and get useful information
         sym_set_warm_start(env, ws);

         sym_warm_solve(env);
         sym_get_obj_val(env, &new_ub);
      }
      //Changing UB of last variable if better bound found
      if (-new_ub <= orig_ub[i-1] - etol) {
         sym_set_col_upper(env, i-1, -new_ub);
         orig_ub[i-1] = -new_ub;
         total_bound_changes++;
      }
      printf("\nMAIN: Done solving all min/max bounding problems in refinement %d\n\n", j);

      if (total_bound_changes >= threshold_bound_changes) {
         //Reset total_bound_changes
         total_bound_changes = 0;

         //Changing objective function back to minimizing first coefficient
         sym_set_obj_coeff(env, i-1, 0);
         sym_set_obj_coeff(env, 0, 1);
         //Now, solve the problem and get useful information
         sym_set_warm_start(env, ws);

         sym_warm_solve(env);
         sym_get_obj_val(env, &new_lb);
      } else {
         break;
      }
   }

   FREE(ws);
   sym_close_environment(env);
}


#endif
