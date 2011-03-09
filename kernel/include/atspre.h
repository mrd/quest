#ifndef _ATSPRE_H_
#define _ATSPRE_H_

#include "types.h"

typedef uint32 ats_ulint_type;
typedef uint32 ats_uint32_type;
typedef sint32 ats_int_type;
typedef uint32 ats_uint_type;
typedef uint16 ats_usint_type;
typedef uint8  ats_uchar_type;
typedef uint8  ats_uint8_type;
typedef void * ats_ptr_type;
typedef void * ats_ref_type;
typedef void * ats_clo_ref_type;
typedef void * ats_clo_ptr_type;
typedef void * ats_fun_ptr_type;
typedef void ats_void_type;
typedef bool ats_bool_type;

#define atspre_ilt atspre_lt_int_int
#define atspre_ilte atspre_lte_int_int
#define atspre_igt atspre_gt_int_int
#define atspre_igte atspre_gte_int_int
#define atspre_igt atspre_gt_int_int
#define atspre_ieq atspre_eq_int_int
#define atspre_ineq atspre_neq_int_int

#define atspre_icompare atspre_compare_int_int
#define atspre_imax atspre_max_int_int
#define atspre_imin atspre_min_int_int

#define ATS_MALLOC(x) (void *)0
#define ATS_GC_MARKROOT(x,y) ;

static inline ats_bool_type
atspre_ilt (ats_int_type a, ats_int_type b)
{
  return (a < b);
}

static inline ats_int_type
atspre_iadd (ats_int_type a, ats_int_type b)
{
  return (a + b);
}

static ats_ptr_type atspre_null_ptr = (ats_ptr_type)0;

static inline ats_bool_type
atspre_gt_int_int (ats_int_type i1, ats_int_type i2)
{
  return (i1 > i2) ;
}

static inline ats_bool_type
atspre_eq_int_int (ats_int_type i1, ats_int_type i2) 
{
  return (i1 == i2) ;
}

static inline ats_bool_type
atspre_lte_int_int (ats_int_type i1, ats_int_type i2) 
{
  return (i1 <= i2) ;
}

static inline ats_bool_type
atspre_gte_int_int (ats_int_type i1, ats_int_type i2) 
{
  return (i1 >= i2) ;
}

static inline ats_int_type
atspre_compare_int_int (ats_int_type i1, ats_int_type i2) 
{
  if (i1 < i2) return (-1) ;
  else if (i1 > i2) return ( 1) ;
  else return (0) ;
}

static inline ats_int_type
atspre_max_int_int (ats_int_type i1, ats_int_type i2) 
{
  return (i1 >= i2) ? i1 : i2 ;
}

static inline ats_int_type
atspre_min_int_int (ats_int_type i1, ats_int_type i2) 
{
  return (i1 <= i2) ? i1 : i2 ;
}

static inline ats_uint_type
atspre_uint_of_int (ats_int_type i) 
{
  return i ;
}

static inline ats_uint_type
atspre_uint_of_uint8 (ats_uint8_type i)
{
  return i ;
}

static inline ats_uint8_type
atspre_uint8_of_uint (ats_uint_type i)
{
  return i ;
}

static inline ats_int_type
atspre_int_of_uint (ats_uint_type i)
{
  return i ;
}

static inline ats_int_type
atspre_int1_of_int (ats_int_type i)
{
  return i ;
}

static inline ats_bool_type
atspre_peq (const ats_ptr_type p1, const ats_ptr_type p2) 
{
  return (p1 == p2) ;
}

static inline ats_bool_type
atspre_pneq (const ats_ptr_type p1, const ats_ptr_type p2) 
{
  return (p1 != p2) ;
}

static inline ats_int_type
atspre_compare_ptr_ptr (const ats_ptr_type p1, const ats_ptr_type p2)
{
  if (p1 < p2) return (-1) ;
  else if (p1 > p2) return ( 1) ;
  else return (0) ;  
}

static inline ats_void_type
panic_if (ats_bool_type b)
{
  void panic (char *);
  if (b)
    panic ("panic_if");
}

static inline ats_void_type
panic_ifnot (ats_bool_type b)
{
  void panic (char *);
  if (!b)
    panic ("panic_ifnot");
}

#endif
