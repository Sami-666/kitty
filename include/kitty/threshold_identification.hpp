/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
  
#pragma once
#include "isop.hpp"
#include "operations.hpp"
#include "algorithm.hpp"
#include <vector>
#include <fstream>
#include <iostream>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"


namespace kitty
{
  // unate_in_var returns true if the function is unate in a single variable , false if not
 template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
 bool unate_in_var( TT& tt, uint8_t var ) 
{
  /*uint8_t numvars = tt.num_vars();*/
    /* co-factor */
    auto const tt1 = cofactor0( tt, var );
    auto const tt2 = cofactor1( tt, var );
      if ( binary_predicate( tt1, tt2, std::greater_equal<>()) || binary_predicate( tt1,tt2, std ::less_equal<>()) )
      {
         return true; 
      }
      else
      {
        return false;
      }
}
// neg_unate_in_var returns true if the function is negative unate in a single variable , false if not
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool neg_unate_in_var(const TT& tt, uint8_t var)
{ 
     /* co-factor */
     auto const tt2 = cofactor0( tt, var );
     auto const tt1 = cofactor1( tt, var );
     if (binary_predicate( tt1,tt2, std ::less_equal<>() )){
       return true; 

   }
   return false; 

}


template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  uint8_t numvars = tt.num_vars();
  TT tt_copy = tt;  // tt_copy  will be built to be equal to the function  f*


  std::vector<int64_t> linear_form(numvars + 1, 0);
  std::vector<bool> negative_unate(numvars, false); // a vector of booleans that will define the type of uunateness of the function for each variable.

  //  Check if the given function is unate 
  for ( uint8_t i(0); i < numvars; ++i )
  {
    if (! unate_in_var(tt_copy, i) )return false;


    if ( neg_unate_in_var(tt,i))
    {
      negative_unate[i] = true;// This vector stores the original type of unateness  in each variable 

      flip_inplace(tt_copy, i); // so as we obtain a positive unate function in all the variables.
      
      
    }
  }
  //  if the function is unate: Create constraints
  // to speed up the ILP part, we can work on the irredundant SOP representations.

std:: vector<cube>   ONset (isop(tt_copy)); 
std:: vector<cube>   OFFset (isop(~tt_copy)); 
// the model is built row by row , so in the beginning we will start by creating a model with 0 rows and numvars + 1 columns
   auto lp = make_lp( 0, numvars + 1 );  // numvars+1= number of columns comprising the varables and threshold 

   set_verbose( lp, 1 );

  std::vector<REAL> row(numvars + 2, 0);
  row[numvars + 1] = -1; // Threshold
  REAL *Obj_fun = &row[0]; // pointer to the objective function :An array with 1+column elements that contains the values of the objective function.

  // construct rows for ONset
  for ( auto &cube: ONset )
  {
    for ( auto i = 0u; i < numvars; ++i )
    {
      if ( cube.get_mask(i) && cube.get_bit(i) )
        row[i + 1] = 1; // vector on which we will apply the ON_constraits 
      else
        row[i + 1] = 0;
    }
    add_constraint(lp, Obj_fun, GE, 0);  
  }

  // construct rows for OFFset
  for ( auto &cube: OFFset )
  {
    for ( auto i = 0u; i < numvars; ++i )
    {
      if ( !cube.get_mask(i) || cube.get_bit(i) )
        row[i + 1] = 1;
      else
        row[i + 1] = 0;
    }
    add_constraint(lp, Obj_fun, LE, -1);
  }


  for ( auto i = 1u; i <= numvars + 1; ++i )
  {
    row[i] = 1;
  }
  set_obj_fn( lp, Obj_fun ); 




  if ( solve( lp ) == INFEASIBLE )
    return false;



  if ( plf )
  {
    // recuperate the solution for f*
    REAL *solution; 
    get_ptr_variables( lp, &solution );
   // change the weights corresponding  to  the variables where the original function is negative unate . 
    
    for ( auto var = 0u; var < numvars + 1; ++var )
       linear_form[var] = solution[var];

     for ( auto var = 0u; var < numvars; ++var )
      
       if ( negative_unate[var] ) {
         linear_form.back() -= linear_form[var];
         linear_form[var] = -linear_form[var];
       }

     plf->swap(linear_form);
   
   }
  return true;


  if (lp != 0) {
        /* clean up such that all used memory by lpsolve is freed */
        delete_lp(lp);
      }

  //write_lp(lp, "model.lp");
}
} /* namespace kitty */
