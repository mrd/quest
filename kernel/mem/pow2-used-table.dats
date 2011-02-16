//
// credit goes here ...
//

%{^
#include "atspre.h"
#include "mem/pow2.hats"
#include "mem/pow2.h"
%}

// #define ATS_DYNLOADFLAG 0
#define ATS_DYNLOADFUN_NAME "pow2_used_table_dynload"

(* ****** ****** *)

staload "SATS/mem/pow2.sats"

(* ****** ****** *)

staload M = "util/linmap_avltree_ngc.dats"

(* ****** ****** *)

typedef key = ptr
typedef itm = uint8
viewtypedef table_vt = $M.map_vt (key,itm)

// [compare_ptr_ptr] is now implemented in [pointer.cats]
implement $M.compare_key_key<key> (x1, x2, cmp) = compare_ptr_ptr (x1, x2)

(* ****** ****** *)

viewtypedef avlnode = $M.avlnode (key, itm)
extern fun avlnode_alloc ():<> [l:addr] (avlnode? @ l | ptr l)
  = "avlnode_alloc"
extern fun avlnode_free {l:addr} (pf: avlnode? @ l | p: ptr l):<> void
  = "avlnode_free"

%{^
ats_ptr_type 
avlnode_alloc () 
{
  ats_ptr_type pow2_get_free_block (ats_int_type);
  return pow2_get_free_block (POW2_MIN_POW);
}

ats_void_type 
avlnode_free (ats_ptr_type block) 
{
  ats_void_type pow2_add_free_block (ats_ptr_type, ats_int_type);
  pow2_add_free_block (block, POW2_MIN_POW);
}

%}

(* ****** ****** *)

fn pow2_insert_used_table_main (
    m: &table_vt, key:ptr, idx:uint8, cmp: $M.cmp key
  ) :<> [err:int | err <= 0] int err = let
  val (pf_node | p_node) = avlnode_alloc ()
  val () = p_node->key := key
  val () = p_node->itm := idx
  val tag = $M.linmap_insert (pf_node | m, p_node, cmp)
in
  if tag then let
    prval Some_v pf_node = pf_node
    val () = avlnode_free (pf_node | p_node)
  in
    ~1 (* failure *)
  end else let
    prval None_v () = pf_node in 0 (* success *)
  end // end of [if]
end (* end of [pow2_insert_used_table_main] *)

(* ****** ****** *)

fn pow2_remove_used_table_main (
    m: &table_vt
  , key:ptr, idx: &uint8? >> opt (uint8, err==0)
  , cmp: $M.cmp key
  ) :<> #[err:int | err <= 0] int (err) = let
  val (pf_node | p_node) = $M.linmap_remove (m, key, cmp)
in
  if p_node <> null then let
    prval Some_v pf_node = pf_node
    val () = idx := p_node->itm
    prval () = opt_some {itm} (idx)
    val () = avlnode_free (pf_node | p_node)
  in
    0 // success
  end else let
    prval None_v () = pf_node
    prval () = opt_none {itm} (idx)
  in
    ~1 // failure
  end (* end of [if] *)
end (* end of [pow2_insert_used_table_main] *)

(* ****** ****** *)

local

var the_used_table
  : table_vt = $M.linmap_empty<> {key,itm} ()
// end of [the_used_table]

prval pf_the_used_table = view@ the_used_table
prval () = // this makes sure that [the_used_table] cannot be used alone!
  __POW2_LOCK_v_absorb (pf_the_used_table) where {
  extern prfun __POW2_LOCK_v_absorb {v:view} (pf: v):<> void
} // end of [prval]

assume POW2_USED_TABLE_v = table_vt @ the_used_table

in // in of [local]

(*
fun pow2_insert_used_table {i:pow2idx}
  (pf: !POW2_USED_TABLE_v | blk: !free_block_vt i, idx: int i):<> void
*)

implement pow2_insert_used_table (pf | blk, idx) = let
  val cmp = $extval ($M.cmp key, "0")
  val key = ptr_of_free_block (blk)
  val itm = uint8_of_uint (uint_of_int idx)
in
  pow2_insert_used_table_main (the_used_table, key, itm, cmp)
end // end of [pow2_insert_used_table]

(*
fun pow2_remove_used_table {i:pow2idx}
  (pf: !POW2_USED_TABLE_v | blk: !free_block_vt i, idx: &int? >> int i):<> void
*)

implement pow2_remove_used_table {i} (pf | blk, idx) = let
  val cmp = $extval ($M.cmp key, "0")
  val key = ptr_of_free_block (blk)
  var idx1: uint8 // uninitialized
  val err = pow2_remove_used_table_main (the_used_table, key, idx1, cmp)
in
  if :(idx1: uint8?) =>
    err = 0 then let // success
    prval () = opt_unsome (idx1)
    val idx1 = uint_of_uint8 (idx1)
    val [i1:int] idx1 = int1_of_int (int_of_uint idx1) // casting
    prval () = __assert () where {
      extern prfun __assert ():<> [i==i1] void // ??? // this is something that is not verified!!!
    } // end of [prval]
    val () = idx := idx1
    prval () = opt_some {int i} (idx)
  in
    0 // success
  end else let // failure
    prval () = opt_unnone (idx1)
    prval () = opt_none {int i} (idx) in err
  end (* end of [if] *)
end // end of [pow2_remove_used_table]

end // end of [local]

(* ****** ****** *)

(* end of [kernel-mem-pow2-used-table.dats] *)
