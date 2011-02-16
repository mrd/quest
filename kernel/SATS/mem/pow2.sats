//
// memory allocation/deallocation for QUEST kernel
//

//
// credit goes here ...
//

%{#
#include "atspre.h"
%}

(* ****** ****** *)

#include "include/mem/pow2.hats"

(* ****** ****** *)

sortdef anz = {a:addr | a <> null}

sortdef pow2idx = {
  i:int | POW2_MIN_POW <= i; i <= POW2_MAX_POW
} // end of [pow2idx]

sortdef pow2idx1 = {
  i:int | POW2_MIN_POW < i; i <= POW2_MAX_POW
} // end of [pow2idx]

(* ****** ****** *)

absviewt@ype POW2_HEADER_vt0ype
  (l:addr, cnt:int) = $extype "POW2_HEADER_vt0ype"
// end of [POW2_HEADER_vt0ype]

absview POW2_HEADER_list_v (n:int, l:addr)

(* ****** ****** *)

absviewtype free_block_vt (int) = $extype "ats_ptr_type"
viewtypedef Free_block_vt = [i:int] free_block_vt i
castfn ptr_of_free_block {i:int} (blk: !free_block_vt i):<> ptr

(* ****** ****** *)

absview POW2_TABLE_v

absview POW2_USED_TABLE_v

absview POW2_LOCK_v

(* ****** ****** *)

stadef POW2_HEADER_vt = POW2_HEADER_vt0ype

fun POW2_HEADER_cnt_get {l0:addr} {l:addr} {cnt:nat}
  (pf: !POW2_HEADER_vt (l, cnt) @ l0 | p: ptr l0):<> int cnt
  = "POW2_HEADER_cnt_get"
// end of [POW2_HEADER_cnt_get]

fun POW2_HEADER_nxt_get {l0:addr} {l:addr} {cnt:nat}
  (pf: !POW2_HEADER_vt (l, cnt) @ l0 | p: ptr l0) :<> ptr l
  = "POW2_HEADER_nxt_get"
// end of [POW2_HEADER_nxt_get]

fun POW2_HEADER_nxt_set {l0:addr} {l,l_nxt:addr} {cnt:nat} (
    pf: !POW2_HEADER_vt (l, cnt) @ l0 >> POW2_HEADER_vt (l_nxt, cnt) @ l0
  | p: ptr l0, p_nxt: ptr l_nxt
  ) :<> void
  = "POW2_HEADER_nxt_set"
// end of [POW2_HEADER_nxt_set]

(* ****** ****** *)

viewtypedef POW2_HEADER_vt
  (l:addr) = [cnt:pos] POW2_HEADER_vt (l:addr, cnt:int)
// end of [POW2_HEADER_vt]

fun POW2_HEADER_alloc ()
  :<> [l0:addr] (POW2_HEADER_vt (null, 0) @ l0 | ptr l0)
  = "POW2_HEAD_alloc"
// end of [POW2_HEADER_alloc]

fun POW2_HEADER_free {l0:addr}
  {l:addr} (pf: POW2_HEADER_vt (l, 0) @ l0 | p0: ptr l0):<> void
  = "POW2_HEAD_free"
// end of [POW2_HEADER_free]

(* ****** ****** *)

viewtypedef POW2_HEADER_list =
  [n:nat] [l:addr] (POW2_HEADER_list_v (n:int, l:addr) | ptr l)
// end of [POW2_HEADER_list]

prfun POW2_HEADER_list_v_nil ():<prf> POW2_HEADER_list_v (0, null)

prfun POW2_HEADER_list_v_cons {n:nat} {l0,l1:addr}
  (pf1: POW2_HEADER_vt (l1) @ l0, pf2: POW2_HEADER_list_v (n, l1))
  :<prf> POW2_HEADER_list_v (n+1, l0)

prfun POW2_HEADER_list_unnil {n:nat}
  (pf: POW2_HEADER_list_v (n, null)):<> [n==0] void
// end of [POW2_HEADER_list_unnil]

prfun POW2_HEADER_list_v_uncons {n:nat}
  {l0:anz} (pf: POW2_HEADER_list_v (n, l0))
  :<> [l1:addr | n > 0] (POW2_HEADER_vt l1 @ l0, POW2_HEADER_list_v (n-1, l1))
// end of [POW2_HEADER_list_uncons]

fun POW2_HEADER_list_uncons {n:nat}
  {l0:anz} (pf: POW2_HEADER_list_v (n, l0) | p0: ptr l0)
  :<> [l1:addr | n > 0] (
    POW2_HEADER_vt l1 @ l0, POW2_HEADER_list_v (n-1, l1) | ptr l1
  )
// end of [POW2_HEADER_list_uncons]

(* ****** ****** *)

fun pow2_table_takeout
  {i:pow2idx}
  (pf: POW2_TABLE_v | i: int i)
  :<> [l:addr] (
    POW2_HEADER_list @ l
  , POW2_HEADER_list @ l -<lin,prf> POW2_TABLE_v
  | ptr l
  ) = "pow2_table_takeout"
// end of [pow2_table_takeout]

prfun POW2_TABLE_v_of_POW2_LOCK_v (pf: POW2_LOCK_v)
  :<prf> (POW2_TABLE_v, POW2_TABLE_v -<lin,prf> POW2_LOCK_v)
// end of ...

(* ****** ****** *)

prfun POW2_USED_TABLE_v_of_POW2_LOCK_v (pf: POW2_LOCK_v)
  :<prf> (POW2_USED_TABLE_v, POW2_USED_TABLE_v -<lin,prf> POW2_LOCK_v)
// end of ...

fun pow2_insert_used_table {i:pow2idx}
  (pf: !POW2_USED_TABLE_v | blk: !free_block_vt i, idx: int i)
  :<> #[err:int | err <= 0] int err

fun pow2_remove_used_table {i:pow2idx}
  (pf: !POW2_USED_TABLE_v | blk: !free_block_vt i, idx: &int? >> opt (int i, err==0))
  :<> #[err:int | err <= 0] int err

(* ****** ****** *)

fun pow2_lock_acquire ():<> (POW2_LOCK_v | void)
  = "pow2_lock_acquire"

fun pow2_lock_release (pf: POW2_LOCK_v | (*none*)):<> void
  = "pow2_lock_release"

(* ****** ****** *)

// these functions should be declared elsewhere ...
fun panic_if {b:bool} (b: bool b):<> [b==false] void = "panic_if"
fun panic_ifnot {b:bool} (b: bool b):<> [b==true] void = "panic_ifnot"

(* ****** ****** *)

fun pow2_alloc
  (sz: uint32, blk: &Free_block_vt? >> free_block_vt i): #[i:pow2idx] int i
  = "pow2_alloc"

fun pow2_free {i:pow2idx} (blk: free_block_vt i): void
  = "pow2_free"

(* ****** ****** *)

(* end of [kernel-mem-pow2.sats] *)
