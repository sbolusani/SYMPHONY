/*===========================================================================*/
/*                                                                           */
/* This file is part of the SYMPHONY Branch, Cut, and Price Library.         */
/*                                                                           */
/* SYMPHONY was jointly developed by Ted Ralphs (ted@lehigh.edu) and         */
/* Laci Ladanyi (ladanyi@us.ibm.com).                                        */
/*                                                                           */
/* (c) Copyright 2000-2013 Ted Ralphs. All Rights Reserved.                  */
/*                                                                           */
/* This software is licensed under the Eclipse Public License. Please see    */
/* accompanying file for terms.                                              */
/*                                                                           */
/*===========================================================================*/

#ifndef _CUT_GEN_USER_H
#define _CUT_GEN_USER_H

/* SYMPHONY include files */
#include "sym_types.h"
#include "sym_proto.h"

/* CBLP include files */
#include "cblp.h"


/*===========================================================================*/
/*========================= Other user subroutines =========================*/
/*===========================================================================*/

void generate_disjunctive_cuts PROTO((user_problem *prob, int varnum,
		   double objval, int *indices, double *values,
		   double etol, int *num_cuts, int *alloc_cuts,
		   cut_data ***cuts));

#endif
