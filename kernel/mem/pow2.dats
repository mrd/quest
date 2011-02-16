//
// memory allocation/deallocation for QUEST kernel
//

//
// credit goes here ...
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

staload "SATS/mem/pow2.sats"
dynload "mem/pow2-used-table.dats"

(* ****** ****** *)

%{^

#include "types.h"
#include "atspre.h"
#include "smp/spinlock.h"
#include "mem/physical.h"
#include "mem/virtual.h"
#include "arch/i386.h"

%}

(* ****** ****** *)

%{^
#define POW2_MIN_POW 5
#define POW2_MIN_SIZE (1 << POW2_MIN_POW)
%}


%{^
#define POW2_MAX_POW 16
#define POW2_MAX_SIZE (1 << POW2_MAX_POW)
%}

#include "mem/pow2.hats"

(* ****** ****** *)

/*
** NB: the value of POW2_MAX_POW has to be smaller than 2^POW2_MIN_POW
** because it needs to be able to fit within the POW2_MASK_POW.  Also keep
** in mind it needs to be able to find a contiguous virtual address range
** every time it allocates one of these large blocks.
*/
#assert (POW2_MAX_POW < (1 << POW2_MIN_POW))

#define POW2_MIN_SIZE (1<<POW2_MIN_POW)
#define POW2_MAX_SIZE (1<<POW2_MAX_POW)

/*
** the length of the central header table
*/
#define POW2_TABLE_LEN ((POW2_MAX_POW - POW2_MIN_POW)+1)

/*
** the numbe of frames in a max-size block
*/
#define POW2_MAX_POW_FRAMES (1 << (POW2_MAX_POW - 12))

/*
** for masking the index from a descriptor:
*/
#define POW2_MASK_POW ((1<<POW2_MIN_POW)-1)

(* ****** ****** *)

%{^

struct POW2_HEADER_struct {
  struct POW2_HEADER_struct *next;
  uint32 count;
  uint8 *ptrs[0];
} ;

typedef struct POW2_HEADER_struct POW2_HEADER_vt0ype;

#define POW2_MAX_COUNT ((0x1000 - sizeof(POW2_HEADER_vt0ype)) >> 2)

static inline
ats_int_type
POW2_HEADER_cnt_get (ats_ptr_type p0) {
  return ((POW2_HEADER_vt0ype*)p0)->count ;
}

static inline
ats_ptr_type
POW2_HEADER_nxt_get (ats_ptr_type p0) {
  return ((POW2_HEADER_vt0ype*)p0)->next ;
}

static inline
ats_void_type
POW2_HEADER_nxt_set
(ats_ptr_type p0, ats_ptr_type p_nxt) {
  ((POW2_HEADER_vt0ype*)p0)->next = p_nxt ; return ;
}

%}

sta POW2_MAX_COUNT : int
extern praxi POW2_MAX_COUNT_gtz ():<prf> [POW2_MAX_COUNT > 0] void
macdef POW2_MAX_COUNT = $extval (int (POW2_MAX_COUNT), "POW2_MAX_COUNT")

(* ****** ****** *)

implement POW2_HEADER_list_uncons (pf | p0) = let
  prval (pf1, pf2) = POW2_HEADER_list_v_uncons (pf)
  val p1 = POW2_HEADER_nxt_get (pf1 | p0)
in
  (pf1, pf2 | p1)
end // end of [POW2_HEADER_list_uncons]

(* ****** ****** *)

%{^

#define POW2_TABLE_LEN ((POW2_MAX_POW - POW2_MIN_POW)+1)
static POW2_HEADER_vt0ype *pow2_table[POW2_TABLE_LEN] ;

static inline
ats_ptr_type
pow2_table_takeout (ats_int_type i) { return &pow2_table[i - POW2_MIN_POW] ; }

%}

(* ****** ****** *)

%{^

static inline
ats_void_type
pow2_add_free_block_ins (
  ats_ptr_type p0, ats_ptr_type blk
) {
  uint32 cnt ;
  cnt = ((POW2_HEADER_vt0ype*)p0)->count ;
  ((POW2_HEADER_vt0ype*)p0)->ptrs[cnt] = blk ;
  ((POW2_HEADER_vt0ype*)p0)->count = cnt + 1 ;
  return ;
} /* end of [pow2_add_free_block_ins] */

%}

extern
fun pow2_add_free_block_ins
  {i:pow2idx} {l0:addr} {l:addr}
  {cnt:nat | cnt < POW2_MAX_COUNT} (
    pf: !POW2_HEADER_vt (l, cnt) @ l0 >> POW2_HEADER_vt (l, cnt+1) @ l0
  | p0: ptr l0, blk: free_block_vt i
  ) :<> void
  = "pow2_add_free_block_ins"

fun pow2_add_free_block_loop
  {i:pow2idx} {n:nat} {l:anz} .<n>. (
    pf: !POW2_HEADER_list_v (n, l)
          >> POW2_HEADER_list_v (n1, l)
  | p: ptr l, blk: free_block_vt i, idx: int i
  ) :<> #[n1:nat] void = let
  val (pf1, pf2 | p_nxt) = POW2_HEADER_list_uncons (pf | p)
in
  if p_nxt <> null then let
    val () = pow2_add_free_block_loop (pf2 | p_nxt, blk, idx)
    prval () = pf := POW2_HEADER_list_v_cons (pf1, pf2)
  in
    // nothing
  end else let
    val cnt = POW2_HEADER_cnt_get (pf1 | p)
  in
    if cnt < POW2_MAX_COUNT then let
      val () = pow2_add_free_block_ins (pf1 | p, blk)
      prval () = pf := POW2_HEADER_list_v_cons (pf1, pf2)
    in
      // nothing
    end else let
      val (pf_nxt | p_nxt) = POW2_HEADER_alloc ()
      prval () = POW2_MAX_COUNT_gtz ()
      val () = pow2_add_free_block_ins (pf_nxt | p_nxt, blk)
      val () = POW2_HEADER_nxt_set (pf1 | p, p_nxt)
      prval pf2 = POW2_HEADER_list_v_cons (pf_nxt, pf2)
      prval () = pf := POW2_HEADER_list_v_cons (pf1, pf2)
    in
      // nothing
    end (* end of [if] *)
  end // end of [if]
end (* end of [pow2_add_free_block_loop] *)

(* ****** ****** *)

extern fun pow2_add_free_block {i:pow2idx} (
    pf_pow2_table: !POW2_TABLE_v | blk: free_block_vt i, idx: int i
  ) :<> void = "pow2_add_free_block"
  
implement pow2_add_free_block (pf_pow2_table | blk, idx) = let
  val (pf0, fpf_pow2_table | p0) = pow2_table_takeout (pf_pow2_table | idx)
  val (pf | p) = !p0
  val () = if p <> null then let
    val () = pow2_add_free_block_loop (pf | p, blk, idx)
    prval () = p0->0 := pf
    prval () = pf_pow2_table := fpf_pow2_table (pf0)
  in
    // nothing
  end else let
    val (pf1 | p1) = POW2_HEADER_alloc ()
    prval () = POW2_MAX_COUNT_gtz ()
    val () = pow2_add_free_block_ins (pf1 | p1, blk)
    prval pf = POW2_HEADER_list_v_cons (pf1, pf)
    prval () = p0->0 := pf; val () = p0->1 := p1
    prval () = pf_pow2_table := fpf_pow2_table (pf0)
  in
    // nothing
  end (* end of [val] *)
in
  // nothing
end // end of [pow2_add_free_block]

(* ****** ****** *)

//
// allocating a free block ...
//
extern fun pow2_make_free_block ():<> free_block_vt (POW2_MAX_POW)
  = "pow2_make_free_block"

(* ****** ****** *)

%{

void *
pow2_split_free_block
  (ats_ptr_type blk, ats_int_type idx) {
  return ((uint8*)blk) + (1 << (idx - 1));
}

%}

extern fun pow2_split_free_block {i:pow2idx1}
  (blk: !free_block_vt i >> free_block_vt (i-1), idx: int i):<> free_block_vt (i-1)
  = "pow2_split_free_block"

(* ****** ****** *)

%{^

static inline
ats_ptr_type
pow2_get_free_block_rem (ats_ptr_type p0) {
  ats_ptr_type blk ; uint32 cnt ;
  cnt = ((POW2_HEADER_vt0ype*)p0)->count ;
  blk = ((POW2_HEADER_vt0ype*)p0)->ptrs[cnt - 1] ;
  ((POW2_HEADER_vt0ype*)p0)->count = cnt - 1 ;
  return blk ;
} /* end of [pow2_add_free_block_rem] */

%}

extern fun
pow2_get_free_block_rem
  {i:pow2idx} {l0:addr} {l:addr} {cnt:pos} (
    pf: !POW2_HEADER_vt (l, cnt) @ l0 >> POW2_HEADER_vt (l, cnt-1) @ l0
  | p0: ptr l0
  ) :<> free_block_vt (i)
  = "pow2_get_free_block_rem"

(* ****** ****** *)

fun pow2_get_free_block_loop
  {i:pow2idx} {l0:addr} {n:nat} {l:anz} {cnt:nat} .<n>. (
    pf1: !POW2_HEADER_vt (l, cnt) @ l0
           >> POW2_HEADER_vt (l1, cnt) @ l0
  , pf2: !POW2_HEADER_list_v (n, l) >> POW2_HEADER_list_v (n1, l1)
  | p0: ptr l0, p: ptr l, idx: int i
  ) :<> #[n1:nat;l1:addr] free_block_vt (i) = let
  val (pf21, pf22 | p_nxt) = POW2_HEADER_list_uncons (pf2 | p)
in
  if p_nxt <> null then let
    val blk = pow2_get_free_block_loop (pf21, pf22 | p, p_nxt, idx)
    prval () = pf2 := POW2_HEADER_list_v_cons (pf21, pf22)
  in
    blk
  end else let
    val blk = pow2_get_free_block_rem (pf21 | p)
    val cnt = POW2_HEADER_cnt_get (pf21 | p)
  in
    if cnt > 0 then let
      prval () = pf2 := POW2_HEADER_list_v_cons (pf21, pf22)
    in
      blk
    end else let
      val () = POW2_HEADER_free (pf21 | p)
      val () = POW2_HEADER_nxt_set (pf1 | p0, null)
      prval () = pf2 := pf22
    in
      blk
    end (* end of [if] *)
  end // end of [if]
end (* end of [pow2_get_free_block_loop] *)

(* ****** ****** *)

fun pow2_get_free_block {i:pow2idx} .<POW2_MAX_POW-i>.
  (pf_pow2_table: !POW2_TABLE_v | idx: int i):<> free_block_vt i = let
  val (pf0, fpf_pow2_table | p0) = pow2_table_takeout (pf_pow2_table | idx)
  val (pf | p) = !p0
in
  if p <> null then let
    val (pf1, pf2 | p_nxt) = POW2_HEADER_list_uncons (pf | p)
  in
    if p_nxt <> null then let
      val blk = pow2_get_free_block_loop (pf1, pf2 | p, p_nxt, idx)
      prval () = p0->0 := POW2_HEADER_list_v_cons (pf1, pf2)
      prval () = pf_pow2_table := fpf_pow2_table (pf0)
    in
      blk
    end else let
      val blk = pow2_get_free_block_rem (pf1 | p)
      val cnt = POW2_HEADER_cnt_get (pf1 | p)
    in
      if cnt > 0 then let
        prval () = p0->0 := POW2_HEADER_list_v_cons (pf1, pf2)
        prval () = pf_pow2_table := fpf_pow2_table (pf0)
      in
        blk
      end else let
        val () = POW2_HEADER_free (pf1 | p)
        prval () = p0->0 := pf2; val () = p0->1 := null
        prval () = pf_pow2_table := fpf_pow2_table (pf0)
      in
        blk
      end // end of [if]
    end (* end of [if] *)
  end else begin
    if idx < POW2_MAX_POW then let
      val idx1 = idx + 1
      prval () = p0->0 := pf
      prval () = pf_pow2_table := fpf_pow2_table (pf0)
      val blk = pow2_get_free_block (pf_pow2_table | idx1)
      val blk1 = pow2_split_free_block (blk, idx1)
      val () = pow2_add_free_block (pf_pow2_table | blk, idx)
    in
      blk1
    end else let
      prval () = p0->0 := pf
      prval () = pf_pow2_table := fpf_pow2_table (pf0)
    in
      pow2_make_free_block () // loop returns
    end (* end of [if] *)
  end (* end of [if] *)
end // end of [pow2_get_free_block]

extern fun pow2_get_free_block_C {i:pow2idx}
  (pf_pow2_table: !POW2_TABLE_v | idx: int i):<> free_block_vt i
  = "pow2_get_free_block"
implement pow2_get_free_block_C (pf_pow2_table | idx) =
  pow2_get_free_block (pf_pow2_table | idx)

(* ****** ****** *)

%{^

static
ats_int_type
pow2_compute_index (uint32 sz)
{
  int i;
  if (sz <= POW2_MIN_SIZE)
    return POW2_MIN_POW ;
  else if (sz >= POW2_MAX_SIZE)
    return POW2_MAX_POW ;
  else {
    sz-- ;
    /* bsr: find most significant set bit */
    asm volatile ("bsrl %1,%0":"=r" (i):"r" (sz));
    return (i + 1);
  } // end of [if]
} /* end of [pow2_compute_index] */

%}

extern fun
pow2_compute_index (size: uint32): [i:pow2idx] int i
  = "pow2_compute_index"

(* ****** ****** *)

%{^

spinlock pow2_lock = SPINLOCK_INIT;

ats_void_type
pow2_lock_acquire () {
  spinlock_lock (&pow2_lock) ; return ;
}

ats_void_type
pow2_lock_release () {
  spinlock_unlock (&pow2_lock) ; return ;
}

%}

(* ****** ****** *)

implement pow2_alloc
  (sz, blk) = idx where {
  val idx = pow2_compute_index (sz)
  val (pf_lock | ()) = pow2_lock_acquire ()
  prval (pf_table, fpf_lock) = POW2_TABLE_v_of_POW2_LOCK_v (pf_lock)
  val () = blk := pow2_get_free_block (pf_table | idx)
  prval pf_lock = fpf_lock (pf_table)
  prval (pf_used_table, fpf_lock) = POW2_USED_TABLE_v_of_POW2_LOCK_v (pf_lock)
  val err = pow2_insert_used_table (pf_used_table | blk, idx)
  val () = panic_ifnot (err = 0) // should we continue if err <> 0?
  prval pf_lock = fpf_lock (pf_used_table)
  val () = pow2_lock_release (pf_lock | (*none*))
} // end of [pow2_alloc]

implement pow2_free (blk) = () where {
  var idx: int // uninitialized
  val ptr = ptr_of_free_block (blk)
  val (pf_lock | ()) = pow2_lock_acquire ()
  prval (pf_used_table, fpf_lock) = POW2_USED_TABLE_v_of_POW2_LOCK_v (pf_lock)
  val err = pow2_remove_used_table (pf_used_table | blk, idx)
  prval pf_lock = fpf_lock (pf_used_table)
  val () = panic_ifnot (err = 0) // should we continue if err <> 0?
  prval () = opt_unsome (idx)
  prval (pf_table, fpf_lock) = POW2_TABLE_v_of_POW2_LOCK_v (pf_lock)
  val () = pow2_add_free_block (pf_table | blk, idx)
  prval pf_lock = fpf_lock (pf_table)
  val () = pow2_lock_release (pf_lock | (*none*))
} // end of [pow2_free]

(* ****** ****** *)

%{$

void
pow2_init (void)
{
  int i;
  /*
  for (i = 0; i < POW2_TABLE_LEN; i++) {
    pow2_table[i] = map_virtual_page (alloc_phys_frame () | 3);
    memset (pow2_table[i], 0, 0x1000);
  }
  */

  memset (pow2_table, 0, POW2_TABLE_LEN);
  pow2_used_table_dynload ();
  /*  
  pow2_used_table = map_virtual_page (alloc_phys_frame () | 3); 
  memset (pow2_used_table, 0, 0x1000); 
  pow2_used_count = 0;
  pow2_used_table_pages = 1; 
  */
}

/* How many frames to allocate for a max-size block: */
#define POW2_MAX_POW_FRAMES (1 << (POW2_MAX_POW - 12))
static uint32 pow2_tmp_phys_frames[POW2_MAX_POW_FRAMES];

ats_ptr_type
pow2_make_free_block (void)
{
  int i;
  for (i = 0; i < POW2_MAX_POW_FRAMES; i++)
    pow2_tmp_phys_frames[i] = alloc_phys_frame () | 3;
  return map_virtual_pages (pow2_tmp_phys_frames, POW2_MAX_POW_FRAMES);
}

ats_ptr_type 
POW2_HEAD_alloc () 
{
  void *page = map_virtual_page (alloc_phys_frame () | 3);
  memset (page, 0, 0x1000);
  return page;
}

ats_void_type 
POW2_HEAD_free (ats_ptr_type block) 
{
  uint32 frame = (uint32)get_phys_addr (block);
  unmap_virtual_page (block);
  free_phys_frame (frame);
}


%}

(* ****** ****** *)

(* end of [kernel-mem-pow2.dats] *)
